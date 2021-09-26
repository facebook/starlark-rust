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

use crate::values::{AllocFrozenValue, FrozenHeap, FrozenHeapRef, FrozenValue, Value};
use gazebo::prelude::*;
use std::{fmt, fmt::Display};

/// A [`FrozenValue`] along with a [`FrozenHeapRef`] that ensures it is kept alive.
/// Obtained from [`FrozenModule::get`](crate::environment::FrozenModule::get) or
/// [`OwnedFrozenValue::alloc`].
///
/// While it is possible to obtain the underlying [`FrozenValue`] with
/// [`unchecked_frozen_value`](OwnedFrozenValue::unchecked_frozen_value), that approach
/// is strongly discouraged. See the other methods which unpack the code, access it as a
/// [`Value`] (which has a suitable lifetime) or add references to other heaps.
#[derive(Debug, Clone, Dupe)]
pub struct OwnedFrozenValue {
    owner: FrozenHeapRef,
    // Invariant: this FrozenValue must be kept alive by the `owner` field.
    value: FrozenValue,
}

impl Display for OwnedFrozenValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.value, f)
    }
}

impl OwnedFrozenValue {
    /// Create an [`OwnedFrozenValue`] - generally [`OwnedFrozenValue`]s are obtained
    /// from [`FrozenModule::get`](crate::environment::FrozenModule::get).
    /// Safe provided the `value` (and any values it points at) are kept alive by the
    /// `owner`, typically because the value was created on the heap.
    ///
    /// ```
    /// use starlark::values::{FrozenHeap, OwnedFrozenValue};
    /// let heap = FrozenHeap::new();
    /// let value = heap.alloc("test");
    /// unsafe { OwnedFrozenValue::new(heap.into_ref(), value) };
    /// ```
    pub unsafe fn new(owner: FrozenHeapRef, value: FrozenValue) -> Self {
        Self { owner, value }
    }

    /// Create an [`OwnedFrozenValue`] in a new heap.
    pub fn alloc(x: impl AllocFrozenValue) -> Self {
        let heap = FrozenHeap::new();
        let val = heap.alloc(x);
        // Safe because we just created the value on the heap
        unsafe { Self::new(heap.into_ref(), val) }
    }

    /// Unpack the boolean contained in the underlying value, or [`None`] if it is not a boolean.
    pub fn unpack_bool(&self) -> Option<bool> {
        self.value.unpack_bool()
    }

    /// Unpack the int contained in the underlying value, or [`None`] if it is not an int.
    pub fn unpack_int(&self) -> Option<i32> {
        self.value.unpack_int()
    }

    /// Unpack the string contained in the underlying value, or [`None`] if it is not an string.
    pub fn unpack_str(&self) -> Option<&str> {
        self.value.unpack_str()
    }

    /// Obtain the [`Value`] stored inside.
    pub fn value<'v>(&'v self) -> Value<'v> {
        Value::new_frozen(self.value)
    }

    /// Extract a [`Value`] by passing the [`FrozenHeap`] which will promise to keep it alive.
    /// When using with a [`Module`](crate::environment::Module),
    /// see the [`frozen_heap`](crate::environment::Module::frozen_heap) function.
    /// If you don't care about the resulting lifetime the [`value`](OwnedFrozenValue::value) method is easier.
    pub fn owned_value<'v>(&self, heap: &'v FrozenHeap) -> Value<'v> {
        // Safe because we convert it to a value which is tied to the owning heap
        unsafe { self.owned_frozen_value(heap).to_value() }
    }

    /// Operate on the [`FrozenValue`] stored inside.
    /// Safe provided you don't store the argument [`FrozenValue`] after the closure has returned.
    /// Using this function is discouraged when possible.
    pub fn map(&self, f: impl FnOnce(FrozenValue) -> FrozenValue) -> Self {
        Self {
            owner: self.owner.dupe(),
            value: f(self.value),
        }
    }

    /// Same as [`map`](OwnedFrozenValue::map) above but with [`Result`]
    pub fn try_map<E>(
        &self,
        f: impl FnOnce(FrozenValue) -> Result<FrozenValue, E>,
    ) -> Result<Self, E> {
        Ok(Self {
            owner: self.owner.dupe(),
            value: f(self.value)?,
        })
    }

    /// Obtain a reference to the FrozenHeap that owns this value.
    pub fn owner(&self) -> &FrozenHeapRef {
        &self.owner
    }

    /// Obtain direct access to the [`FrozenValue`] that lives inside. If you drop all
    /// references to the [`FrozenHeap`] keeping it alive, any code using the [`FrozenValue`]
    /// is likely to segfault. If possible use [`value`](OwnedFrozenValue::value) or
    /// [`owned_frozen_value`](OwnedFrozenValue::owned_frozen_value).
    pub unsafe fn unchecked_frozen_value(&self) -> FrozenValue {
        self.value
    }

    /// Extract a [`FrozenValue`] by passing the [`FrozenHeap`] which will keep it alive.
    /// Provided the argument heap does indeed stay alive for the lifetime of the result,
    /// all will be fine. Unsafe if you pass the wrong heap, or don't keep the heap alive
    /// long enough. Where possible, use [`value`](OwnedFrozenValue::value) or
    /// [`owned_value`](OwnedFrozenValue::owned_value).
    pub unsafe fn owned_frozen_value(&self, heap: &FrozenHeap) -> FrozenValue {
        heap.add_reference(&self.owner);
        self.value
    }
}
