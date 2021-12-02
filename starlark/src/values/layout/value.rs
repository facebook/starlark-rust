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

use std::marker::PhantomData;

use either::Either;
use gazebo::{
    cast,
    coerce::{Coerce, CoerceKey},
    prelude::*,
};

use crate::{
    collections::SmallHashResult,
    values::{
        layout::{
            arena::{AValueHeader, AValueRepr},
            avalue::{
                basic_ref, AValue, AValueDyn, StarlarkStrAValue, VALUE_FALSE, VALUE_NONE,
                VALUE_TRUE,
            },
            pointer::{FrozenPointer, Pointer},
            pointer_i32::PointerI32,
        },
        num::Num,
        string::StarlarkStr,
        UnpackValue, VALUE_EMPTY_STRING,
    },
};

/// A Starlark value. The lifetime argument `'v` corresponds to the [`Heap`](crate::values::Heap) it is stored on.
///
/// Many of the methods simply forward to the underlying [`StarlarkValue`](crate::values::StarlarkValue).
/// The [`Display`](std::fmt::Display) trait is equivalent to the `repr()` function in Starlark.
#[derive(Clone_, Copy_, Dupe_)]
// One possible change: moving to Forward during GC.
pub struct Value<'v>(pub(crate) Pointer<'v, AValueHeader>);

unsafe impl<'v> Coerce<Value<'v>> for Value<'v> {}
unsafe impl<'v> CoerceKey<Value<'v>> for Value<'v> {}

/// A [`Value`] that can never be changed. Can be converted back to a [`Value`] with [`to_value`](FrozenValue::to_value).
///
/// A [`FrozenValue`] exists on a [`FrozenHeap`](crate::values::FrozenHeap), which in turn can be kept
/// alive by a [`FrozenHeapRef`](crate::values::FrozenHeapRef). If the frozen heap gets dropped
/// while a [`FrozenValue`] from it still exists, the program will probably segfault, so be careful
/// when working directly with [`FrozenValue`]s. See the type [`OwnedFrozenValue`](crate::values::OwnedFrozenValue)
/// for a little bit more safety.
#[derive(Clone, Copy, Dupe)]
// One possible change: moving from Blackhole during GC
pub struct FrozenValue(pub(crate) FrozenPointer<'static, AValueHeader>);

// These can both be shared, but not obviously, because we hide a fake RefCell in Pointer to stop
// it having variance.
unsafe impl Send for FrozenValue {}
unsafe impl Sync for FrozenValue {}

impl<'v> Value<'v> {
    pub(crate) fn new_ptr(x: &'v AValueHeader, is_str: bool) -> Self {
        Self(Pointer::new_unfrozen(x, is_str))
    }

    pub(crate) fn new_ptr_query_is_str(x: &'v AValueHeader) -> Self {
        let is_string = x.unpack().is_str();
        Self::new_ptr(x, is_string)
    }

    pub(crate) fn new_repr<T: AValue<'v>>(x: &'v AValueRepr<T>) -> Self {
        Self::new_ptr(&x.header, T::is_str())
    }

    pub(crate) fn new_ptr_usize_with_str_tag(x: usize) -> Self {
        Self(Pointer::new_unfrozen_usize_with_str_tag(x))
    }

    /// Create a new `None` value.
    pub fn new_none() -> Self {
        FrozenValue::new_none().to_value()
    }

    /// Create a new boolean.
    pub fn new_bool(x: bool) -> Self {
        FrozenValue::new_bool(x).to_value()
    }

    /// Create a new integer.
    pub fn new_int(x: i32) -> Self {
        FrozenValue::new_int(x).to_value()
    }

    /// Create a new blank string.
    pub(crate) fn new_empty_string() -> Self {
        FrozenValue::new_empty_string().to_value()
    }

    /// Turn a [`FrozenValue`] into a [`Value`]. See the safety warnings on
    /// [`OwnedFrozenValue`](crate::values::OwnedFrozenValue).
    pub fn new_frozen(x: FrozenValue) -> Self {
        // Safe if every FrozenValue must have had a reference added to its heap first.
        // That property is NOT statically checked.
        Self(x.0.to_pointer())
    }

    /// Obtain the underlying [`FrozenValue`] from inside the [`Value`], if it is one.
    pub fn unpack_frozen(self) -> Option<FrozenValue> {
        if self.0.is_unfrozen() {
            None
        } else {
            Some(FrozenValue(unsafe {
                self.0.cast_lifetime().to_frozen_pointer()
            }))
        }
    }

    /// Is this value `None`.
    pub fn is_none(self) -> bool {
        // Safe because frozen values never have a tag
        self.0.ptr_value() == cast::ptr_to_usize(&VALUE_NONE)
    }

    /// Obtain the underlying numerical value, if it is one.
    pub fn unpack_num(self) -> Option<Num> {
        Num::unpack_value(self)
    }

    /// Obtain the underlying `bool` if it is a boolean.
    pub fn unpack_bool(self) -> Option<bool> {
        let p = self.0.ptr_value();
        if p == cast::ptr_to_usize(&VALUE_TRUE) {
            Some(true)
        } else if p == cast::ptr_to_usize(&VALUE_FALSE) {
            Some(false)
        } else {
            None
        }
    }

    /// Obtain the underlying `int` if it is an integer.
    pub fn unpack_int(self) -> Option<i32> {
        self.0.unpack_int()
    }

    pub(crate) fn is_str(self) -> bool {
        self.0.is_str()
    }

    /// Like [`unpack_str`](Value::unpack_str), but gives a pointer to a boxed string.
    /// Mostly useful for when you want to convert the string to a `dyn` trait, but can't
    /// form a `dyn` of an unsized type.
    ///
    /// Unstable and likely to be removed in future, as the presence of the `Box` is
    /// not a guaranteed part of the API.
    pub fn unpack_starlark_str(self) -> Option<&'v StarlarkStr> {
        if self.is_str() {
            unsafe {
                Some(
                    &self
                        .0
                        .unpack_ptr_no_int_unchecked()
                        .as_repr::<StarlarkStrAValue>()
                        .payload
                        .1,
                )
            }
        } else {
            None
        }
    }

    /// Obtain the underlying `str` if it is a string.
    pub fn unpack_str(self) -> Option<&'v str> {
        self.unpack_starlark_str().map(|s| s.unpack())
    }

    /// Get a pointer to a [`AValue`].
    pub(crate) fn get_ref(self) -> &'v dyn AValueDyn<'v> {
        match self.0.unpack() {
            Either::Left(x) => x.unpack(),
            Either::Right(x) => basic_ref(PointerI32::new(x)),
        }
    }

    pub(crate) fn get_hash(self) -> anyhow::Result<SmallHashResult> {
        self.get_ref().get_hash()
    }

    /// Are two [`Value`]s equal, looking at only their underlying pointer. This function is
    /// low-level and provides two guarantees.
    ///
    /// 1. It is _reflexive_, the same [`Value`] passed as both arguments will result in [`true`].
    /// 2. If this function is [`true`], then [`Value::equals`] will also consider them equal.
    ///
    /// Note that other properties are not guaranteed, and the result is not considered part of the API.
    /// The result can be impacted by optimisations such as hash-consing, copy-on-write, partial
    /// evaluation etc.
    pub fn ptr_eq(self, other: Self) -> bool {
        self.0.ptr_eq(other.0)
    }

    /// Returns an identity for this [`Value`], derived from its pointer. This function is
    /// low-level and provides two guarantees. Those are valid until the next GC:
    ///
    /// 1. Calling it mulitple times on the same [`Value`]  will return [`ValueIdentity`] that
    ///    compare equal.
    /// 2. If two [`Value]` have [`ValueIdentity`]  that compare equal, then [`Value::ptr_eq`] and
    ///    [`Value::equals`]  will also consider them to be equal.
    pub fn identity(self) -> ValueIdentity<'v> {
        ValueIdentity {
            identity: self.0.ptr_value(),
            phantom: PhantomData,
        }
    }

    /// Get the underlying pointer.
    /// Should be done sparingly as it slightly breaks the abstraction.
    /// Most useful as a hash key based on pointer.
    /// For external users, `Value::identity` returns an opaque `ValueIdentity` that makes fewer
    /// guarantees.
    pub(crate) fn ptr_value(self) -> usize {
        self.0.ptr_value()
    }
}

impl FrozenValue {
    pub(crate) fn new_ptr(x: &'static AValueHeader, is_str: bool) -> Self {
        Self(FrozenPointer::new_frozen(x, is_str))
    }

    pub(crate) fn new_repr<'a, T: AValue<'a>>(x: &'static AValueRepr<T>) -> Self {
        Self::new_ptr(&x.header, T::is_str())
    }

    pub(crate) fn new_ptr_usize_with_str_tag(x: usize) -> Self {
        Self(FrozenPointer::new_frozen_usize_with_str_tag(x))
    }

    /// Create a new value representing `None` in Starlark.
    pub fn new_none() -> Self {
        Self::new_repr(&VALUE_NONE)
    }

    /// Create a new boolean in Starlark.
    pub fn new_bool(x: bool) -> Self {
        if x {
            Self::new_repr(&VALUE_TRUE)
        } else {
            Self::new_repr(&VALUE_FALSE)
        }
    }

    /// Create a new int in Starlark.
    pub fn new_int(x: i32) -> Self {
        Self(FrozenPointer::new_int(x))
    }

    /// Create a new empty string.
    pub(crate) fn new_empty_string() -> Self {
        VALUE_EMPTY_STRING.unpack()
    }

    /// Is a value a Starlark `None`.
    pub fn is_none(self) -> bool {
        // Safe because frozen values never have a tag
        self.0.ptr_value() == cast::ptr_to_usize(&VALUE_NONE)
    }

    /// Return the [`bool`] if the value is a boolean, otherwise [`None`].
    pub fn unpack_bool(self) -> Option<bool> {
        let p = self.0.ptr_value();
        if p == cast::ptr_to_usize(&VALUE_TRUE) {
            Some(true)
        } else if p == cast::ptr_to_usize(&VALUE_FALSE) {
            Some(false)
        } else {
            None
        }
    }

    /// Return the int if the value is an integer, otherwise [`None`].
    pub fn unpack_int(self) -> Option<i32> {
        self.0.unpack_int()
    }

    pub(crate) fn is_str(self) -> bool {
        self.to_value().is_str()
    }

    // The resulting `str` is alive as long as the `FrozenHeap` is,
    // but we don't have that lifetime available to us. Therefore,
    // we cheat a little, and use the lifetime of the `FrozenValue`.
    // Because of this cheating, we don't expose it outside Starlark.
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub(crate) fn unpack_str<'v>(&'v self) -> Option<&'v str> {
        self.to_value().unpack_str()
    }

    /// Get a pointer to the [`AValue`] object this value represents.
    pub(crate) fn get_ref<'v>(self) -> &'v dyn AValueDyn<'v> {
        match self.0.unpack() {
            Either::Left(x) => x.unpack(),
            Either::Right(x) => basic_ref(PointerI32::new(x)),
        }
    }
}

/// An opaque value representing the identity of a given Value. Two values have the same identity
/// if and only if [`Value::ptr_eq`] would return [`true`] on them.
#[derive(Eq, PartialEq, Copy, Clone, Dupe, Hash)]
pub struct ValueIdentity<'v> {
    identity: usize,
    phantom: PhantomData<&'v ()>,
}

#[test]
fn test_send_sync()
where
    FrozenValue: Send + Sync,
{
}
