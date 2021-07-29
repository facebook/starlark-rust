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
        arena::AValuePtr,
        avalue::{basic_ref, AValue},
        pointer::{Pointer, PointerUnpack},
        pointer_i32::PointerI32,
    },
    none::NoneType,
    string::StarlarkStr,
};
use gazebo::prelude::*;
use void::Void;

// So we can provide &dyn StarlarkValue's when we need them
const VALUE_NONE: NoneType = NoneType;
const VALUE_TRUE: bool = true;
const VALUE_FALSE: bool = false;

/// A Starlark value. The lifetime argument `'v` corresponds to the [`Heap`](crate::values::Heap) it is stored on.
///
/// Many of the methods simply forward to the underlying [`StarlarkValue`](crate::values::StarlarkValue).
#[derive(Clone_, Copy_, Dupe_)]
// One possible change: moving to Forward during GC.
pub struct Value<'v>(pub(crate) Pointer<'v, 'v, AValuePtr, AValuePtr>);

/// A [`Value`] that can never be changed. Can be converted back to a [`Value`] with [`to_value`](FrozenValue::to_value).
///
/// A [`FrozenValue`] exists on a [`FrozenHeap`](crate::values::FrozenHeap), which in turn can be kept
/// alive by a [`FrozenHeapRef`](crate::values::FrozenHeapRef). If the frozen heap gets dropped
/// while a [`FrozenValue`] from it still exists, the program will probably segfault, so be careful
/// when working directly with [`FrozenValue`]s. See the type [`OwnedFrozenValue`](crate::values::OwnedFrozenValue)
/// for a little bit more safety.
#[derive(Clone, Copy, Dupe)]
// One possible change: moving from Blackhole during GC
pub struct FrozenValue(pub(crate) Pointer<'static, 'static, AValuePtr, Void>);

// These can both be shared, but not obviously, because we hide a fake RefCell in Pointer to stop
// it having variance.
unsafe impl Send for FrozenValue {}
unsafe impl Sync for FrozenValue {}

impl<'v> Value<'v> {
    /// Create a new `None` value.
    pub fn new_none() -> Self {
        Self(Pointer::new_none())
    }

    /// Create a new boolean.
    pub fn new_bool(x: bool) -> Self {
        Self(Pointer::new_bool(x))
    }

    /// Create a new integer.
    pub fn new_int(x: i32) -> Self {
        Self(Pointer::new_int(x))
    }

    /// Turn a [`FrozenValue`] into a [`Value`]. See the safety warnings on
    /// [`OwnedFrozenValue`](crate::values::OwnedFrozenValue).
    pub fn new_frozen(x: FrozenValue) -> Self {
        // Safe if every FrozenValue must have had a reference added to its heap first.
        // That property is NOT statically checked.
        let p = unsafe {
            transmute!(
                Pointer<'static, 'static, AValuePtr, Void>,
                Pointer<'v, 'static, AValuePtr, Void>,
                x.0
            )
        };
        Self(p.coerce())
    }

    /// Obtain the underlying [`FrozenValue`] from inside the [`Value`], if it is one.
    pub fn unpack_frozen(self) -> Option<FrozenValue> {
        unsafe {
            transmute!(
                Option<Pointer<'v, 'v, AValuePtr, Void>>,
                Option<Pointer<'static, 'static, AValuePtr, Void>>,
                self.0.coerce_opt()
            )
            .map(FrozenValue)
        }
    }

    /// Is this value `None`.
    pub fn is_none(self) -> bool {
        self.0.is_none()
    }

    /// Obtain the underlying `bool` if it is a boolean.
    pub fn unpack_bool(self) -> Option<bool> {
        self.0.unpack_bool()
    }

    /// Obtain the underlying `int` if it is an integer.
    pub fn unpack_int(self) -> Option<i32> {
        self.0.unpack_int()
    }

    /// Like [`unpack_str`](Value::unpack_str), but gives a pointer to a boxed string.
    /// Mostly useful for when you want to convert the string to a `dyn` trait, but can't
    /// form a `dyn` of an unsized type.
    ///
    /// Unstable and likely to be removed in future, as the presence of the `Box` is
    /// not a guaranteed part of the API.
    pub fn unpack_starlark_str(self) -> Option<&'v StarlarkStr> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => x.unpack().unpack_starlark_str(),
            PointerUnpack::Ptr2(x) => x.unpack().unpack_starlark_str(),
            _ => None,
        }
    }

    /// Obtain the underlying `str` if it is a string.
    pub fn unpack_str(self) -> Option<&'v str> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => x.unpack().unpack_str(),
            PointerUnpack::Ptr2(x) => x.unpack().unpack_str(),
            _ => None,
        }
    }

    /// Get a pointer to a [`AValue`].
    pub fn get_ref(self) -> &'v dyn AValue<'v> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => x.unpack(),
            PointerUnpack::Ptr2(x) => x.unpack(),
            PointerUnpack::None => basic_ref(&VALUE_NONE),
            PointerUnpack::Bool(true) => basic_ref(&VALUE_TRUE),
            PointerUnpack::Bool(false) => basic_ref(&VALUE_FALSE),
            PointerUnpack::Int(x) => basic_ref(PointerI32::new(x)),
        }
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

    /// Get the underlying pointer.
    /// Should be done sparingly as it slightly breaks the abstraction.
    /// Most useful as a hash key based on pointer.
    pub(crate) fn ptr_value(self) -> usize {
        self.0.ptr_value()
    }
}

impl FrozenValue {
    /// Create a new value representing `None` in Starlark.
    pub fn new_none() -> Self {
        Self(Pointer::new_none())
    }

    /// Create a new boolean in Starlark.
    pub fn new_bool(x: bool) -> Self {
        Self(Pointer::new_bool(x))
    }

    /// Create a new int in Starlark.
    pub fn new_int(x: i32) -> Self {
        Self(Pointer::new_int(x))
    }

    /// Is a value a Starlark `None`.
    pub fn is_none(self) -> bool {
        self.0.is_none()
    }

    /// Return the [`bool`] if the value is a boolean, otherwise [`None`].
    pub fn unpack_bool(self) -> Option<bool> {
        self.0.unpack_bool()
    }

    /// Return the int if the value is an integer, otherwise [`None`].
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
            Some(x) => x.unpack().unpack_str(),
            _ => None,
        }
    }

    /// Get a pointer to the [`AValue`] object this value represents.
    pub fn get_ref<'v>(self) -> &'v dyn AValue<'v> {
        match self.0.unpack() {
            PointerUnpack::Ptr1(x) => x.unpack(),
            PointerUnpack::Ptr2(x) => void::unreachable(*x),
            PointerUnpack::None => basic_ref(&VALUE_NONE),
            PointerUnpack::Bool(true) => basic_ref(&VALUE_TRUE),
            PointerUnpack::Bool(false) => basic_ref(&VALUE_FALSE),
            PointerUnpack::Int(x) => basic_ref(PointerI32::new(x)),
        }
    }
}

#[test]
fn test_send_sync()
where
    FrozenValue: Send + Sync,
{
}
