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
// Preallocate int, none, bool etc slots in Value, so they are shared
// Encoding none, bool etc in the pointer of frozen value

use crate::{
    collections::Hashed,
    values::{
        layout::{
            arena::{AValueHeader, Arena, HeapSummary, Reservation},
            avalue::{complex, simple, starlark_str, AValue},
            constant::constant_string,
            value::{FrozenValue, Value},
        },
        string::hash_string_result,
        AllocFrozenValue, ComplexValue, SimpleValue,
    },
};
use either::Either;
use gazebo::{cast, prelude::*};
use std::{
    cell::RefCell,
    collections::HashSet,
    fmt,
    fmt::{Debug, Formatter},
    hash::{Hash, Hasher},
    intrinsics::copy_nonoverlapping,
    marker::PhantomData,
    ops::Deref,
    ptr,
    sync::Arc,
    usize,
};

/// A heap on which [`Value`]s can be allocated. The values will be annotated with the heap lifetime.
#[derive(Default)]
pub struct Heap {
    arena: RefCell<Arena>,
}

impl Debug for Heap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut x = f.debug_struct("Heap");
        x.field(
            "bytes",
            &self.arena.try_borrow().map(|x| x.allocated_bytes()),
        );
        x.finish()
    }
}

/// A heap on which [`FrozenValue`]s can be allocated.
/// Can be kept alive by a [`FrozenHeapRef`].
#[derive(Default)]
pub struct FrozenHeap {
    arena: Arena,                          // My memory
    refs: RefCell<HashSet<FrozenHeapRef>>, // Memory I depend on
}

/// `FrozenHeap` when it is no longer modified and can be share between threads.
/// Although, `arena` is not safe to share between threads, but at least `refs` is.
#[derive(Default)]
struct FrozenFrozenHeap {
    arena: Arena,
    refs: HashSet<FrozenHeapRef>,
}

impl Debug for FrozenHeap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut x = f.debug_struct("FrozenHeap");
        x.field("bytes", &self.arena.allocated_bytes());
        x.field("refs", &self.refs.try_borrow().map(|x| x.len()));
        x.finish()
    }
}

impl Debug for FrozenFrozenHeap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut x = f.debug_struct("FrozenHeap");
        x.field("bytes", &self.arena.allocated_bytes());
        x.field("refs", &self.refs.len());
        x.finish()
    }
}

// Safe because we never mutate the Arena other than with &mut
unsafe impl Sync for FrozenHeapRef {}
unsafe impl Send for FrozenHeapRef {}

/// A reference to a [`FrozenHeap`] that keeps alive all values on the underlying heap.
/// Note that the [`Hash`] is consistent for a single [`FrozenHeapRef`], but non-deterministic
/// across executions and distinct but observably identical [`FrozenHeapRef`] values.
#[derive(Clone, Dupe, Debug)]
// The Eq/Hash are by pointer rather than value, since we produce unique values
// given an underlying FrozenHeap.
pub struct FrozenHeapRef(Arc<FrozenFrozenHeap>);

impl Hash for FrozenHeapRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let x: &FrozenFrozenHeap = Deref::deref(&self.0);
        ptr::hash(x, state);
    }
}

impl PartialEq<FrozenHeapRef> for FrozenHeapRef {
    fn eq(&self, other: &FrozenHeapRef) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for FrozenHeapRef {}

impl FrozenHeapRef {
    /// Number of bytes allocated on this heap, not including any memory
    /// represented by [`extra_memory`](crate::values::StarlarkValue::extra_memory).
    pub fn allocated_bytes(&self) -> usize {
        self.0.arena.allocated_bytes()
    }

    /// Number of bytes allocated by the heap but not filled.
    /// Note that these bytes will _never_ be filled as no further allocations can
    /// be made on this heap (it has been sealed).
    pub fn available_bytes(&self) -> usize {
        self.0.arena.available_bytes()
    }

    /// Obtain a summary of how much memory is currently allocated by this heap.
    /// Doesn't include the heaps it keeps alive by reference.
    pub fn allocated_summary(&self) -> HeapSummary {
        self.0.arena.allocated_summary()
    }
}

impl FrozenHeap {
    /// Create a new [`FrozenHeap`].
    pub fn new() -> Self {
        Self::default()
    }

    /// After all values have been allocated, convert the [`FrozenHeap`] into a
    /// [`FrozenHeapRef`] which can be [`clone`](Clone::clone)d, shared between threads,
    /// and ensures the underlying values allocated on the [`FrozenHeap`] remain valid.
    pub fn into_ref(self) -> FrozenHeapRef {
        let FrozenHeap { arena, refs } = self;
        FrozenHeapRef(Arc::new(FrozenFrozenHeap {
            arena,
            refs: refs.into_inner(),
        }))
    }

    /// Keep the argument [`FrozenHeapRef`] alive as long as this [`FrozenHeap`]
    /// is kept alive. Used if a [`FrozenValue`] in this heap points at values in another
    /// [`FrozenHeap`].
    pub fn add_reference(&self, heap: &FrozenHeapRef) {
        self.refs.borrow_mut().get_or_insert_owned(heap);
    }

    fn alloc_raw(&self, x: impl AValue<'static>) -> FrozenValue {
        let v: &AValueHeader = self.arena.alloc(x);
        FrozenValue::new_ptr(unsafe { cast::ptr_lifetime(v) })
    }

    /// Allocate a string on this heap. Be careful about the warnings
    /// around [`FrozenValue`].
    pub(crate) fn alloc_str(&self, x: &str) -> FrozenValue {
        if let Some(x) = constant_string(x) {
            x
        } else {
            let v: &AValueHeader = self
                .arena
                .alloc_extra_non_drop(starlark_str(x.len()), x.len());
            unsafe {
                v.write_extra(x.as_bytes())
            };
            FrozenValue::new_ptr(unsafe { cast::ptr_lifetime(v) })
        }
    }

    /// Allocate a string on this heap and hash it. Be careful about the warnings
    /// around [`FrozenValue`].
    pub fn alloc_str_hashed(&self, x: &str) -> Hashed<FrozenValue> {
        let h = hash_string_result(x);
        Hashed::new_unchecked(h, self.alloc_str(x))
    }

    /// Allocate a [`SimpleValue`] on this heap. Be careful about the warnings
    /// around [`FrozenValue`].
    pub fn alloc_simple(&self, val: impl SimpleValue) -> FrozenValue {
        self.alloc_raw(simple(val))
    }

    /// Number of bytes allocated on this heap, not including any memory
    /// represented by [`extra_memory`](crate::values::StarlarkValue::extra_memory).
    pub fn allocated_bytes(&self) -> usize {
        self.arena.allocated_bytes()
    }

    /// Number of bytes allocated by the heap but not yet filled.
    pub fn available_bytes(&self) -> usize {
        self.arena.available_bytes()
    }

    /// Obtain a summary of how much memory is currently allocated by this heap.
    pub fn allocated_summary(&self) -> HeapSummary {
        self.arena.allocated_summary()
    }
}

/// Used to `freeze` values by [`ComplexValue::freeze`].
// A freezer is a pair of the FrozenHeap and a "magic" value,
// which we happen to use for the slots (see `FrozenSlotsRef`)
// but could be used for anything.
pub struct Freezer(FrozenHeap, FrozenValue, Option<Reservation<'static>>);

impl Freezer {
    pub(crate) fn new<T: SimpleValue>(heap: FrozenHeap) -> Self {
        fn reserve<'v, 'v2: 'v, T: AValue<'v2>>(
            heap: &'v FrozenHeap,
            _ty: Option<T>,
        ) -> Reservation<'v> {
            heap.arena.reserve::<T>()
        }

        // Slightly odd construction as we want to produce a reservation with type
        // simple(T), but simple is a function with an opaque impl return, so fake up
        // an empty Option containing the right type.
        let ty: Option<T> = None;
        let ty = ty.map(simple);
        let reservation = reserve(&heap, ty);
        // Morally the type is tied to the heap, but we want to have them both next to each other
        let reservation = unsafe { transmute!(Reservation, Reservation<'static>, reservation) };
        let fv = FrozenValue::new_ptr(unsafe { cast::ptr_lifetime(reservation.ptr()) });
        Self(heap, fv, Some(reservation))
    }

    pub(crate) fn set_magic(&mut self, val: impl SimpleValue) {
        let reservation = self.2.take().expect("Can only call set_magic once");
        reservation.fill(simple(val))
    }

    pub(crate) fn get_magic(&self) -> FrozenValue {
        self.1
    }

    pub(crate) fn into_ref(self) -> FrozenHeapRef {
        self.0.into_ref()
    }

    /// Allocate a new value while freezing. Usually not a great idea.
    pub fn alloc<'v, T: AllocFrozenValue>(&'v self, val: T) -> FrozenValue {
        val.alloc_frozen_value(&self.0)
    }

    pub(crate) fn reserve<'v, 'v2: 'v, T: AValue<'v2>>(&'v self) -> (FrozenValue, Reservation<'v>) {
        let r = self.0.arena.reserve::<T>();
        let fv = FrozenValue::new_ptr(unsafe { cast::ptr_lifetime(r.ptr()) });
        (fv, r)
    }

    /// Freeze a nested value while freezing yourself.
    pub fn freeze(&self, value: Value) -> anyhow::Result<FrozenValue> {
        // Case 1: We have our value encoded in our pointer
        if let Some(x) = value.unpack_frozen() {
            return Ok(x);
        }

        // Case 2: We have already been replaced with a forwarding, or need to freeze
        let value = value.0.unpack_ptr().unwrap();
        match value.unpack_overwrite() {
            Either::Left(x) => Ok(FrozenValue::new_ptr_usize(x)),
            Either::Right(v) => v.heap_freeze(value, self),
        }
    }
}

impl Heap {
    /// Create a new [`Heap`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of bytes allocated on this heap, not including any memory
    /// represented by [`extra_memory`](crate::values::StarlarkValue::extra_memory).
    pub fn allocated_bytes(&self) -> usize {
        self.arena.borrow().allocated_bytes()
    }

    /// Number of bytes allocated by the heap but not yet filled.
    pub fn available_bytes(&self) -> usize {
        self.arena.borrow().available_bytes()
    }

    /// Only those allocated on the inline heap (mostly strings)
    pub(crate) fn allocated_bytes_inline(&self) -> usize {
        self.arena.borrow().allocated_bytes_inline()
    }

    fn alloc_raw<'v, 'v2: 'v2>(&'v self, x: impl AValue<'v2>) -> Value<'v> {
        let arena_ref = self.arena.borrow_mut();
        let arena = &*arena_ref;
        let v: &AValueHeader = arena.alloc(x);

        // We have an arena inside a RefCell which stores ValueMem<'v>
        // However, we promise not to clear the RefCell other than for GC
        // so we can make the `arena` available longer
        Value::new_ptr(unsafe { cast::ptr_lifetime(v) })
    }

    pub(crate) fn alloc_str_init<'v>(
        &'v self,
        len: usize,
        init: impl FnOnce(*mut u8),
    ) -> Value<'v> {
        let arena_ref = self.arena.borrow_mut();
        let arena = &*arena_ref;
        let v: &AValueHeader = arena.alloc_extra_non_drop(starlark_str(len), len);
        init(unsafe { v.get_extra() });

        // We have an arena inside a RefCell which stores ValueMem<'v>
        // However, we promise not to clear the RefCell other than for GC
        // so we can make the `arena` available longer
        Value::new_ptr(unsafe { cast::ptr_lifetime(v) })
    }

    /// Allocate a string on the heap.
    pub fn alloc_str<'v>(&'v self, x: &str) -> Value<'v> {
        if let Some(x) = constant_string(x) {
            x.to_value()
        } else {
            self.alloc_str_init(x.len(), |dest| unsafe {
                copy_nonoverlapping(x.as_ptr(), dest, x.len())
            })
        }
    }

    /// Allocate a string on this heap and hash it.
    pub fn alloc_str_hashed<'v>(&'v self, x: &str) -> Hashed<Value<'v>> {
        let h = hash_string_result(x);
        Hashed::new_unchecked(h, self.alloc_str(x))
    }

    pub(crate) fn alloc_str_concat<'v>(&'v self, x: &str, y: &str) -> Value<'v> {
        // If either strings is empty, we should not be calling this function
        // but reuse non-empty string object instead.
        debug_assert!(!x.is_empty());
        debug_assert!(!y.is_empty());

        self.alloc_str_init(x.len() + y.len(), |dest| unsafe {
            copy_nonoverlapping(x.as_ptr(), dest, x.len());
            copy_nonoverlapping(y.as_ptr(), dest.add(x.len()), y.len())
        })
    }

    pub(crate) fn alloc_char<'v>(&'v self, x: char) -> Value<'v> {
        let mut dst = [0; 4];
        let res = x.encode_utf8(&mut dst);
        self.alloc_str(res)
    }

    /// Allocate a [`SimpleValue`] on the [`Heap`].
    pub fn alloc_simple<'v>(&'v self, x: impl SimpleValue) -> Value<'v> {
        self.alloc_raw(simple(x))
    }

    /// Allocate a [`ComplexValue`] on the [`Heap`].
    pub fn alloc_complex<'v>(&'v self, x: impl ComplexValue<'v>) -> Value<'v> {
        self.alloc_raw(complex(x))
    }

    pub(crate) fn for_each_ordered<'v>(&'v self, mut f: impl FnMut(Value<'v>)) {
        self.arena.borrow_mut().for_each_ordered(|x| {
            // Otherwise the Value is constrainted by the borrow_mut, when
            // we consider values to be kept alive permanently, other than
            // when a GC happens
            f(Value::new_ptr(unsafe { cast::ptr_lifetime(x) }))
        })
    }

    /// Garbage collect any values that are unused. This function is _unsafe_ in
    /// the sense that any `Value<'v>` not returned by `Tracer` _will become
    /// invalid_. Furthermore, any references to values, e.g `&'v str` will
    /// also become invalid.
    pub(crate) unsafe fn garbage_collect<'v>(&'v self, f: impl FnOnce(&Tracer<'v>)) {
        self.garbage_collect_internal(f)
    }

    fn garbage_collect_internal<'v>(&'v self, f: impl FnOnce(&Tracer<'v>)) {
        // Must rewrite all Value's so they point at the new heap
        let mut arena = self.arena.borrow_mut();

        let tracer = Tracer::<'v> {
            arena: Arena::default(),
            phantom: PhantomData,
        };
        f(&tracer);
        *arena = tracer.arena;
    }

    /// Obtain a summary of how much memory is currently allocated by this heap.
    pub fn allocated_summary(&self) -> HeapSummary {
        self.arena.borrow().allocated_summary()
    }
}

/// Used to perform garbage collection by [`Trace::trace`](crate::values::Trace::trace).
pub struct Tracer<'v> {
    arena: Arena,
    phantom: PhantomData<&'v ()>,
}

impl<'v> Tracer<'v> {
    /// Walk over a value during garbage collection.
    pub fn trace(&self, value: &mut Value<'v>) {
        *value = self.adjust(*value)
    }

    pub(crate) fn reserve<'a, 'v2: 'v + 'a, T: AValue<'v2>>(
        &'a self,
    ) -> (Value<'v>, Reservation<'a>) {
        let r = self.arena.reserve::<T>();
        let v = Value::new_ptr(unsafe { cast::ptr_lifetime(r.ptr()) });
        (v, r)
    }

    pub(crate) fn alloc_str(&self, x: &str) -> Value<'v> {
        let v: &AValueHeader = self
            .arena
            .alloc_extra_non_drop(starlark_str(x.len()), x.len());
        unsafe {
            v.write_extra(x.as_bytes())
        };
        Value::new_ptr(unsafe { cast::ptr_lifetime(v) })
    }

    fn adjust(&self, value: Value<'v>) -> Value<'v> {
        // Case 1, doesn't point at the old arena
        if !value.0.is_unfrozen() {
            return value;
        }
        let old_val = value.0.unpack_ptr().unwrap();

        // Case 2: We have already been replaced with a forwarding, or need to freeze
        let res = match old_val.unpack_overwrite() {
            Either::Left(x) => Value::new_ptr_usize(x),
            Either::Right(v) => v.heap_copy(old_val, self),
        };

        res
    }
}

#[test]
fn test_send_sync()
where
    FrozenHeapRef: Send + Sync,
{
}
