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

//! Define the bool type for Starlark.

use crate::values::{
    AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, StarlarkValue, UnpackValue, Value,
    ValueError,
};
use std::cmp::Ordering;

// We'd love to put this on a type, but we use bool directly
pub const BOOL_VALUE_TYPE_NAME: &str = "bool";

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
    fn unpack_value(value: Value, _heap: &Heap) -> Option<Self> {
        value.unpack_bool()
    }
}

/// Define the bool type
impl StarlarkValue<'_> for bool {
    starlark_type!(BOOL_VALUE_TYPE_NAME);

    fn collect_repr(&self, s: &mut String) {
        if *self {
            s.push_str("True")
        } else {
            s.push_str("False")
        }
    }
    fn to_json(&self) -> String {
        if *self {
            "true".to_string()
        } else {
            "false".to_string()
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
