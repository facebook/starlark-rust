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

//! The boolean type (`False` and `True`).
//!
//! Can be created with [`new_bool`](Value::new_bool) and unwrapped with [`unpack_bool`](Value::unpack_bool).
//! Unlike most Starlark values, these aren't actually represented on the [`Heap`], but as special values.

use crate::values::{
    AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, StarlarkValue, UnpackValue, Value,
    ValueError,
};
use std::cmp::Ordering;

/// The result of calling `type()` on booleans.
pub const BOOL_TYPE: &str = "bool";

impl<'v> AllocValue<'v> for bool {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        Value::new_bool(self)
    }
}

impl AllocFrozenValue for bool {
    fn alloc_frozen_value(self, _heap: &FrozenHeap) -> FrozenValue {
        FrozenValue::new_bool(self)
    }
}

impl UnpackValue<'_> for bool {
    fn unpack_value(value: Value) -> Option<Self> {
        value.unpack_bool()
    }
}

/// Define the bool type
impl StarlarkValue<'_> for bool {
    starlark_type!(BOOL_TYPE);

    fn collect_repr(&self, s: &mut String) {
        if *self {
            s.push_str("True")
        } else {
            s.push_str("False")
        }
    }
    fn to_json(&self) -> anyhow::Result<String> {
        if *self {
            Ok("true".to_owned())
        } else {
            Ok("false".to_owned())
        }
    }
    fn to_int(&self) -> anyhow::Result<i32> {
        Ok(if *self { 1 } else { 0 })
    }
    fn to_bool(&self) -> bool {
        *self
    }
    fn get_hash(&self) -> anyhow::Result<u64> {
        Ok(self.to_int().unwrap() as u64)
    }

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        if let Some(other) = other.unpack_bool() {
            Ok(*self == other)
        } else {
            Ok(false)
        }
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        if let Some(other) = other.unpack_bool() {
            Ok(self.cmp(&other))
        } else {
            ValueError::unsupported_with(self, "<>", other)
        }
    }
}
