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

//! The `None` type.

use crate::values::{
    AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, StarlarkValue, UnpackValue, Value,
};
use gazebo::{any::AnyLifetime, prelude::*};

/// Define the None type, use [`NoneType`] in Rust.
#[derive(Debug, Clone, Dupe, AnyLifetime)]
pub struct NoneType;

impl NoneType {
    /// The result of `type(None)`.
    pub const TYPE: &'static str = "NoneType";
}

/// Define the NoneType type
impl<'v> StarlarkValue<'v> for NoneType {
    starlark_type!(NoneType::TYPE);

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        Ok(other.is_none())
    }

    fn collect_repr(&self, s: &mut String) {
        s.push_str("None");
    }

    fn to_json(&self) -> anyhow::Result<String> {
        Ok("null".to_owned())
    }
    fn to_bool(&self) -> bool {
        false
    }
    // just took the result of hash(None) in macos python 2.7.10 interpreter.
    fn get_hash(&self) -> anyhow::Result<u64> {
        Ok(9_223_380_832_852_120_682)
    }
}

impl<'v> AllocValue<'v> for NoneType {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        Value::new_none()
    }
}

impl AllocFrozenValue for NoneType {
    fn alloc_frozen_value(self, _heap: &FrozenHeap) -> FrozenValue {
        FrozenValue::new_none()
    }
}

/// Equivalent of a Rust [`Option`], where [`None`] is encoded as [`NoneType`]. Useful for its [`UnpackValue`] instance.
#[derive(Debug, Eq, PartialEq)]
pub enum NoneOr<T> {
    None,
    Other(T),
}

impl<T> NoneOr<T> {
    /// Convert the [`NoneOr`] to a real Rust [`Option`].
    pub fn into_option(self) -> Option<T> {
        match self {
            Self::None => None,
            Self::Other(x) => Some(x),
        }
    }

    /// Is the value a [`NoneOr::None`].
    pub fn is_none(&self) -> bool {
        matches!(self, NoneOr::None)
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for NoneOr<T> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        if value.is_none() {
            Some(NoneOr::None)
        } else {
            T::unpack_value(value).map(NoneOr::Other)
        }
    }
}
