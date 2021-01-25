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

//! Define the None type for Starlark.

use crate::values::{
    unsupported_with, AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, TypedValue,
    Value,
};
use gazebo::{any::AnyLifetime, prelude::*};
use std::cmp::Ordering;

/// Define the NoneType type
#[derive(Debug, Clone, Dupe, AnyLifetime)]
pub enum NoneType {
    None,
}

pub const NONE: NoneType = NoneType::None;

impl NoneType {
    pub const TYPE: &'static str = "NoneType";
}

/// Define the NoneType type
impl<'v> TypedValue<'v> for NoneType {
    starlark_type!(NoneType::TYPE);

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        Ok(other.is_none())
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        if other.is_none() {
            Ok(Ordering::Equal)
        } else {
            unsupported_with(self, "cmp()", other)
        }
    }

    fn collect_repr(&self, s: &mut String) {
        s.push_str("None");
    }

    fn to_json(&self) -> String {
        "None".to_string()
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

impl<'v> AllocFrozenValue<'v> for NoneType {
    fn alloc_frozen_value(self, _heap: &'v FrozenHeap) -> FrozenValue {
        FrozenValue::new_none()
    }
}
