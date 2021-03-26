/*
 * Copyright 2019 The Starlark in Rust Authors.
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Possible optimisations:
// Avoid the Box duplication
// Encode Int in the pointer too

// We use pointer tagging on the bottom two bits:
// 00 => this Value pointer is actually a FrozenValue pointer
// 01 => this is a real Value pointer
// 11 => this is a bool (next bit: 1 => true, 0 => false)
// 10 => this is a None
//
// We don't use pointer tagging for Int (although we'd like to), because
// our val_ref requires a pointer to the value. We need to put that pointer
// somewhere. The solution is to have a separate value storage vs vtable.

use crate::values::{
    layout::{
        heap::{Freezer, Heap},
        pointer::{Pointer, PointerUnpack},
        pointer_i32::PointerI32,
        thawable_cell::ThawableCell,
    },
    none::NoneType,
    ImmutableValue, MutableValue, TypedValue, ValueError,
};
use either::Either;
use gazebo::{cell::ARef, prelude::*, variants::VariantName};
use static_assertions::assert_eq_size;
use std::{
    cell::{Cell, Ref, RefCell, RefMut},
    time::Instant,
};
use void::Void;

// So we can provide &dyn TypedValue's when we need them
const VALUE_NONE: NoneType = NoneType;
const VALUE_TRUE: bool = true;
const VALUE_FALSE: bool = false;

/// A value that can never be changed, but might have interior mutability.
/// One possible change: moving to Forward during GC.
/// Will not be a `ValueMem::Ref` (see `ValueRef` for that).
#[derive(Clone_, Copy_, Dupe_)]
pub struct Value<'v>(pub(crate) Pointer<'v, 'v, FrozenValueMem, ValueMem<'v>>);

/// A value that might have reference semantics.
/// References are required when a lambda captures an outer variable,
/// as all subsequent modifications of the outer variable will be
/// reflected in the inner.
/// However, most values captured are not by reference, so use the user_tag
/// to indicate whether a value is a `Ref` (and must be dereffed a lot),
/// or just a normal `Value` (much cheaper).
/// A normal `Value` cannot be `ValueMem::Ref`, but this one might be.
#[derive(Clone, Dupe, Debug)]
pub(crate) struct ValueRef<'v>(pub(crate) Cell<Value<'v>>);

// A value that can never be changed
// One possible change: moving from Blackhole during GC
#[derive(Clone, Copy, Dupe)]
pub struct FrozenValue(pub(crate) Pointer<'static, 'static, FrozenValueMem, Void>);

// These can both be shared, but not obviously, because we hide a fake RefCell in Pointer to stop
// it having variance.
unsafe impl Send for FrozenValue {}
unsafe impl Sync for FrozenValue {}

// We care a lot about the size of these data types, so make sure they don't
// regress
assert_eq_size!(FrozenValueMem, [usize; 3]);
assert_eq_size!(ValueMem, [usize; 4]);

#[derive(VariantName)]
pub(crate) enum FrozenValueMem {
    #[allow(dead_code)] // That's the whole point of it
    Uninitialized(Void), // Never created (see Value::Uninitialized)
    Blackhole, // Only occurs during a GC
    Str(Box<str>),
    Immutable(Box<dyn ImmutableValue>), // Not really 'static - but I don't care what
}

fn immutable_typed_value<'a, 'v>(x: &'a dyn ImmutableValue) -> &'a dyn TypedValue<'v> {
    unsafe {
        transmute!(
            &'a dyn TypedValue<'static>,
            &'a dyn TypedValue<'v>,
            x.as_typed_value()
        )
    }
}

#[derive(VariantName)]
pub(crate) enum ValueMem<'v> {
    // Never created, but we often get to ValueMem via dereferencing pointers
    // which have a moderate chance of pointing at 0's, so detect that special case
    // and give a workable error message
    #[allow(dead_code)] // That's the whole point of it
    Uninitialized(Void),
    // Occurs during freezing (for the to-space).
    // Could be encountered normally if someone freezes incrementally
    Forward(FrozenValue),
    // Occurs during GC (for the to-space) - never encountered normally.
    Copied(Value<'v>),
    // Only occurs during GC
    Blackhole,
    // A literal string
    Str(Box<str>),
    // Frozen things that are in my heap (e.g String)
    Immutable(Box<dyn ImmutableValue>),
    // Mutable things in my heap that aren't naturally_mutable()
    Pseudo(Box<dyn MutableValue<'v>>),
    // Mutable things that are in my heap and are naturally_mutable()
    Mutable(RefCell<Box<dyn MutableValue<'v>>>),
    // Thaw on write things that are in my heap and are naturally_mutable()
    // They are either frozen pointers (to be thaw'ed) or normal (point at Mutable)
    ThawOnWrite(ThawableCell<'v>),
    // Used references in slots - usually wrapped in ValueRef
    // Never points at a Ref, must point directly at a real value
    Ref(Cell<Value<'v>>),
    // Used for profiling
    CallEnter(Value<'v>, Instant),
    CallExit(Instant),
}

impl<'v> ValueMem<'v> {
    pub fn unexpected(&self, method: &str) -> ! {
        panic!(
            "ValueMem::{}, unexpected variant {}",
            method,
            self.variant_name()
        )
    }

    fn unpack_str(&self) -> Option<&str> {
        match self {
            Self::Str(x) => Some(x),
            Self::Forward(x) => x.unpack_str(),
            _ => None,
        }
    }

    fn get_ref_mut_already(&self) -> Option<RefMut<dyn MutableValue<'v>>> {
        match self {
            Self::Mutable(x) => match x.try_borrow_mut() {
                Err(_) => None,
                Ok(state) => Some(RefMut::map(state, |x| &mut **x)),
            },
            Self::ThawOnWrite(state) => match state.get_thawed() {
                Some(v) => v.get_ref_mut_already(),
                None => None,
            },
            _ => None,
        }
    }

    fn get_ref_mut(&self, heap: &'v Heap) -> anyhow::Result<RefMut<dyn MutableValue<'v>>> {
        match self {
            Self::Mutable(x) => match x.try_borrow_mut() {
                // Could be called by something else having the ref locked, but iteration is
                // definitely most likely
                Err(_) => Err(ValueError::MutationDuringIteration.into()),
                Ok(state) => Ok(RefMut::map(state, |x| &mut **x)),
            },
            Self::ThawOnWrite(state) => match state.get_thawed() {
                Some(v) => v.get_ref_mut(heap),
                None => match state.thaw(|fv| heap.alloc_mutable_box(fv.thaw())) {
                    None => Err(ValueError::MutationDuringIteration.into()),
                    Some(v) => v.get_ref_mut(heap),
                },
            },
            _ => Err(ValueError::CannotMutateImmutableValue.into()),
        }
    }

    fn get_ref(&self) -> Option<&dyn TypedValue<'v>> {
        match self {
            Self::Forward(x) => Some(x.get_ref()),
            Self::Str(x) => Some(x),
            Self::Immutable(x) => Some(immutable_typed_value(Box::as_ref(x))),
            Self::Pseudo(x) => Some(x.as_typed_value()),
            Self::Mutable(_) => None,
            Self::ThawOnWrite(_) => None,
            _ => self.unexpected("get_ref"),
        }
    }

    pub fn get_aref(&'v self) -> ARef<'v, dyn TypedValue<'v>> {
        match self {
            Self::Forward(x) => ARef::Ptr(x.get_ref()),
            Self::Str(x) => ARef::Ptr(x),
            Self::Immutable(x) => ARef::Ptr(immutable_typed_value(Box::as_ref(x))),
            Self::Pseudo(x) => ARef::Ptr(x.as_typed_value()),
            Self::Mutable(x) => ARef::Ref(Ref::map(x.borrow(), |x| x.as_typed_value())),
            Self::ThawOnWrite(state) => match state.get_ref() {
                Either::Left(fv) => ARef::Ref(Ref::map(fv, |fv| fv.get_ref())),
                Either::Right(v) => v.get_aref(),
            },
            _ => self.unexpected("get_aref"),
        }
    }
}

impl FrozenValueMem {
    fn unexpected(&self, method: &str) -> ! {
        panic!(
            "FrozenValueMem::{}, unexpected variant {}",
            method,
            self.variant_name()
        )
    }

    fn unpack_str(&self) -> Option<&str> {
        match self {
            Self::Str(x) => Some(x),
            _ => None,
        }
    }

    fn get_ref<'v>(&self) -> &dyn TypedValue<'v> {
        match self {
            Self::Str(x) => x,
            Self::Immutable(x) => immutable_typed_value(Box::as_ref(x)),
            _ => self.unexpected("get_ref"),
        }
    }
}

impl<'v> Value<'v> {
    pub fn new_none() -> Self {
        Self(Pointer::new_none())
    }

    pub fn new_bool(x: bool) -> Self {
        Self(Pointer::new_bool(x))
    }

    pub fn new_int(x: i32) -> Self {
        Self(Pointer::new_int(x))
    }

    pub fn new_unassigned() -> Self {
        Self(Pointer::new_unassigned())
    }

    pub fn new_frozen(x: FrozenValue) -> Self {
        // Safe if every FrozenValue must have had a reference added to its heap first.
        // That property is NOT statically checked.
        let p = unsafe {
            transmute!(
                Pointer<'static, 'static, FrozenValueMem, Void>,
                Pointer<'v, 'static, FrozenValueMem, Void>,
                x.0
            )
        };
        Self(p.coerce())
    }

    pub fn unpack_frozen(self) -> Option<FrozenValue> {
        unsafe {
            transmute!(
                Option<Pointer<'v, 'v, FrozenValueMem, Void>>,
                Option<Pointer<'static, 'static, FrozenValueMem, Void>>,
                self.0.coerce_opt()
            )
            .map(FrozenValue)
        }
    }

    pub fn is_none(self) -> bool {
        self.0.is_none()
    }

    pub fn is_unassigned(self) -> bool {
        self.0.is_unassigned()
    }

    pub fn unpack_bool(self) -> Option<bool> {
        self.0.unpack_bool()
    }

    pub fn unpack_int(self) -> Option<i32> {
        self.0.unpack_int()
    }

    pub fn unpack_str(self) -> Option<&'v str> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => x.unpack_str(),
            PointerUnpack::Ptr2(x) => x.unpack_str(),
            _ => None,
        }
    }

    // Get a pointer to a value. Will always be `Some` for `naturally_mutable() == false` things.
    pub fn get_ref(self) -> Option<&'v dyn TypedValue<'v>> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => Some(x.get_ref()),
            PointerUnpack::Ptr2(x) => x.get_ref(),
            PointerUnpack::Unassigned => panic!("get_ref on Unassigned"),
            PointerUnpack::None => Some(&VALUE_NONE),
            PointerUnpack::Bool(true) => Some(&VALUE_TRUE),
            PointerUnpack::Bool(false) => Some(&VALUE_FALSE),
            PointerUnpack::Int(x) => Some(PointerI32::new(x)),
        }
    }

    pub(crate) fn get_aref(self) -> ARef<'v, dyn TypedValue<'v>> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => ARef::Ptr(x.get_ref()),
            PointerUnpack::Ptr2(x) => x.get_aref(),
            PointerUnpack::Unassigned => panic!("get_aref on Unassigned"),
            PointerUnpack::None => ARef::Ptr(&VALUE_NONE),
            PointerUnpack::Bool(x) => ARef::Ptr(if x { &VALUE_TRUE } else { &VALUE_FALSE }),
            PointerUnpack::Int(x) => ARef::Ptr(PointerI32::new(x)),
        }
    }

    // Like get_ref_mut, but only returns a mutable value if it's already mutable
    pub(crate) fn get_ref_mut_already(self) -> Option<RefMut<'v, dyn MutableValue<'v>>> {
        self.0.unpack_ptr2().and_then(|x| x.get_ref_mut_already())
    }

    pub(crate) fn get_ref_mut(
        self,
        heap: &'v Heap,
    ) -> anyhow::Result<RefMut<'v, dyn MutableValue<'v>>> {
        if let Some(x) = self.0.unpack_ptr2() {
            return x.get_ref_mut(heap);
        }
        Err(ValueError::CannotMutateImmutableValue.into())
    }

    /// Equality on the underlying pointer.
    /// Should be done sparingly as it slightly breaks the abstraction.
    pub(crate) fn ptr_eq(self, other: Self) -> bool {
        self.0.ptr_eq(other.0)
    }

    /// Get the underlying pointer.
    /// Should be done sparingly as it slightly breaks the abstraction.
    /// Most useful as a hash key based on pointer.
    pub(crate) fn ptr_value(self) -> usize {
        self.0.ptr_value()
    }
}

impl FrozenValue {
    pub fn new_none() -> Self {
        Self(Pointer::new_none())
    }

    pub fn new_bool(x: bool) -> Self {
        Self(Pointer::new_bool(x))
    }

    pub fn new_int(x: i32) -> Self {
        Self(Pointer::new_int(x))
    }

    pub fn is_none(self) -> bool {
        self.0.is_none()
    }

    pub fn is_unassigned(self) -> bool {
        self.0.is_unassigned()
    }

    pub fn unpack_bool(self) -> Option<bool> {
        self.0.unpack_bool()
    }

    pub fn unpack_int(self) -> Option<i32> {
        self.0.unpack_int()
    }

    // The resulting `str` is alive as long as the `FrozenHeap` is,
    // but we don't have that lifetime available to us. Therefore,
    // we cheat a little, and use the lifetime of the `FrozenValue`.
    // Because of this cheating, we don't expose it outside Starlark.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub(crate) fn unpack_str<'v>(&'v self) -> Option<&'v str> {
        match self.0.unpack_ptr1() {
            Some(x) => x.unpack_str(),
            _ => None,
        }
    }

    pub fn get_ref<'v>(self) -> &'v dyn TypedValue<'v> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => x.get_ref(),
            PointerUnpack::Ptr2(x) => void::unreachable(*x),
            PointerUnpack::Unassigned => panic!("get_ref on Unassigned"),
            PointerUnpack::None => &VALUE_NONE,
            PointerUnpack::Bool(true) => &VALUE_TRUE,
            PointerUnpack::Bool(false) => &VALUE_FALSE,
            PointerUnpack::Int(x) => PointerI32::new(x),
        }
    }

    // Invariant: Only list and dict can be frozen/thaw'ed
    pub(crate) fn thaw<'v>(self) -> Box<dyn MutableValue<'v> + 'v> {
        if let Some(x) = crate::values::list::FrozenList::from_value(&self) {
            x.thaw()
        } else if let Some(x) = crate::values::dict::FrozenDict::from_value(&self) {
            x.thaw()
        } else {
            panic!(
                "FrozenValue.thaw called on a type that wasn't List or Dict, type {}",
                self.get_ref().get_type()
            )
        }
    }
}

impl<'v> ValueRef<'v> {
    // Get the cell, chasing down any forwarding if it exists.
    // We have the invariant that if we have a ref we always set the user tag
    fn get_cell(&self) -> &Cell<Value<'v>> {
        let v = self.0.get();
        if v.0.get_user_tag() {
            match v.0.unpack_ptr2() {
                Some(ValueMem::Ref(cell)) => cell,
                _ => unreachable!(),
            }
        } else {
            &self.0
        }
    }

    pub fn new_unassigned() -> Self {
        Self(Cell::new(Value::new_unassigned()))
    }

    pub fn new_frozen(x: FrozenValue) -> Self {
        Self(Cell::new(Value::new_frozen(x)))
    }

    pub fn set(&self, value: Value<'v>) {
        assert!(!value.0.is_unassigned());
        self.get_cell().set(value);
    }

    pub fn is_unassigned(&self) -> bool {
        self.get().is_none()
    }

    pub fn get(&self) -> Option<Value<'v>> {
        let v = self.get_cell().get();
        if v.0.is_unassigned() { None } else { Some(v) }
    }

    /// Return a new `ValueRef` that points at the same underlying memory as the original.
    /// Updates to either will result in both changing.
    pub fn clone_reference(&self, heap: &'v Heap) -> ValueRef<'v> {
        let v = self.0.get();
        if v.0.get_user_tag() {
            match v.0.unpack_ptr2() {
                Some(ValueMem::Ref(_)) => Self(Cell::new(v)),
                _ => panic!(),
            }
        } else {
            let reffed = Value(heap.alloc_raw(ValueMem::Ref(Cell::new(v))).0.set_user_tag());
            self.0.set(reffed);
            Self(Cell::new(reffed))
        }
    }

    pub fn freeze(&self, freezer: &Freezer) -> FrozenValue {
        freezer.freeze(self.get_cell().get())
    }
}

#[test]
fn test_send_sync()
where
    FrozenValue: Send + Sync,
{
}
