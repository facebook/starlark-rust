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

use crate::{
    environment::Module,
    values::{FrozenHeap, FrozenHeapRef, FrozenValue, Value},
};
use gazebo::prelude::*;
use std::{fmt, fmt::Display};

/// A `FrozenHeapRef` and `FrozenValue`, such that the `FrozenHeapRef` causes the
/// `FrozenValue` to be kept alive. You can extract the value using the
/// `owned_` methods, which require a reference to the heap which should keep the value
/// alive. Or you can use the `unchecked_` methods which require that you know the value
/// remains alive as long as it is used, perhaps because you keep a reference to the
/// containing `OwnedFrozenValue`.
#[derive(Debug, Clone, Dupe)]
pub struct OwnedFrozenValue {
    owner: FrozenHeapRef,
    value: FrozenValue,
}

impl Display for OwnedFrozenValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.value, f)
    }
}

impl OwnedFrozenValue {
    /// Create an `OwnedFrozenValue` - generally `OwnedFrozenValue`'s are obtained
    /// from `FrozenModule.get`.
    pub fn new(owner: FrozenHeapRef, value: FrozenValue) -> Self {
        Self { owner, value }
    }

    /// Extract a `FrozenValue` by passing the heap which will use it.
    /// Unsafe if you pass the wrong heap.
    pub fn owned_frozen_value(&self, heap: &FrozenHeap) -> FrozenValue {
        heap.add_reference(&self.owner);
        self.value
    }

    /// Extract a `Value` by passing the module which will use it.
    pub fn owned_value<'v>(&self, module: &'v Module) -> Value<'v> {
        self.owned_frozen_value(module.frozen_heap()).to_value()
    }

    pub fn unpack_int(&self) -> Option<i32> {
        self.value.unpack_int()
    }

    // Safe provided you don't store the FrozenValue after the closure has returned.
    pub fn map(&self, f: impl FnOnce(FrozenValue) -> FrozenValue) -> Self {
        Self {
            owner: self.owner.dupe(),
            value: f(self.value),
        }
    }

    /// Be VERY careful, potential segfault! See the warnings on `OwnedFrozenValue`.
    pub fn unchecked_frozen_value(&self) -> FrozenValue {
        self.value
    }

    /// Obtain the `Value` stored inside.
    pub fn value<'v>(&'v self) -> Value<'v> {
        Value::new_frozen(self.value)
    }
}
