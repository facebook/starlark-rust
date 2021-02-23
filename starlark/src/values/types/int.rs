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

//! Define the int type for Starlark.

use crate::values::{
    error::ValueError, layout::PointerI32, unsupported_owned, unsupported_with, AllocFrozenValue,
    AllocValue, FrozenHeap, FrozenValue, Heap, TypedValue, Value,
};
use std::cmp::Ordering;

// We'd love to put this on a type, but we use i32 directly
pub const INT_VALUE_TYPE_NAME: &str = "int";

impl<'v> AllocValue<'v> for i32 {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        Value::new_int(self)
    }
}
impl<'v> AllocFrozenValue<'v> for i32 {
    fn alloc_frozen_value(self, _heap: &'v FrozenHeap) -> FrozenValue {
        FrozenValue::new_int(self)
    }
}

fn i64_arith_bin_op<'v, F>(
    left: i32,
    right: Value,
    op: &'static str,
    f: F,
) -> anyhow::Result<Value<'v>>
where
    F: FnOnce(i32, i32) -> anyhow::Result<i32>,
{
    match right.unpack_int() {
        Some(right) => Ok(Value::new_int(f(left, right)?)),
        None => unsupported_owned(INT_VALUE_TYPE_NAME, op, Some(INT_VALUE_TYPE_NAME)),
    }
}

/// Define the int type
impl<'v> TypedValue<'v> for PointerI32 {
    starlark_type!(INT_VALUE_TYPE_NAME);

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        if let Some(other) = other.unpack_int() {
            Ok(self.get() == other)
        } else {
            Ok(false)
        }
    }

    fn collect_repr(&self, s: &mut String) {
        s.push_str(&self.get().to_string());
    }

    fn to_json(&self) -> String {
        self.get().to_string()
    }
    fn to_int(&self) -> anyhow::Result<i32> {
        Ok(self.get())
    }
    fn to_bool(&self) -> bool {
        self.get() != 0
    }
    fn get_hash(&self) -> anyhow::Result<u64> {
        Ok(self.get() as u64)
    }
    fn plus(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(Value::new_int(self.get()))
    }
    fn minus(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get()
            .checked_neg()
            .map(Value::new_int)
            .ok_or_else(|| ValueError::IntegerOverflow.into())
    }
    fn add(&self, _original: Value, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            self.get()
                .checked_add(other)
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into())
        } else {
            unsupported_with(self, "+", other)
        }
    }
    fn sub(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            self.get()
                .checked_sub(other)
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into())
        } else {
            unsupported_with(self, "-", other)
        }
    }
    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_int() {
            Some(other) => self
                .get()
                .checked_mul(other)
                .ok_or_else(|| ValueError::IntegerOverflow.into())
                .map(Value::new_int),
            None => other.mul(Value::new_int(self.get()), heap),
        }
    }
    fn percent(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        i64_arith_bin_op(self.get(), other, "%", |a, b| {
            if b == 0 {
                return Err(ValueError::DivisionByZero.into());
            }
            // In Rust `i32::min_value() % -1` is overflow, but we should eval it to zero.
            if self.get() == i32::min_value() && b == -1 {
                return Ok(0);
            }
            let r = a % b;
            if r == 0 {
                Ok(0)
            } else {
                Ok(if b.signum() != r.signum() { r + b } else { r })
            }
        })
    }
    fn floor_div(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        i64_arith_bin_op(self.get(), other, "//", |a, b| {
            if b == 0 {
                return Err(ValueError::DivisionByZero.into());
            }
            let sig = b.signum() * a.signum();
            let offset = if sig < 0 && a % b != 0 { 1 } else { 0 };
            match a.checked_div(b) {
                Some(div) => Ok(div - offset),
                None => Err(ValueError::IntegerOverflow.into()),
            }
        })
    }

    fn compare(&self, _ptr_eq: bool, other: Value) -> anyhow::Result<Ordering> {
        if let Some(other) = other.unpack_int() {
            Ok(self.get().cmp(&other))
        } else {
            unsupported_with(self, "==", other)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_arithmetic_operators() {
        assert::all_true(
            r#"
+1 == 1
-1 == 0 - 1
1 + 2 == 3
1 - 2 == -1
2 * 3 == 6
5 % 3 == 2
"#,
        );
    }
}
