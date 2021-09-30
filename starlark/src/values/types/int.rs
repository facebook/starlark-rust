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

//! The integer type. Currently limited to 32 bit.
//!
//! Can be created with [`new_int`](Value::new_int) and unwrapped with [`unpack_int`](Value::unpack_int).
//! Unlike most Starlark values, these aren't actually represented on the [`Heap`], but as special values.
//! At some point in the future we plan to support arbitrary sized integers (as required by the
//! [Starlark spec](https://github.com/bazelbuild/starlark/blob/master/spec.md#integers)), and those larger
//! integer values will be stored on the heap.

use crate::values::{
    error::ValueError, layout::PointerI32, num::Num, AllocFrozenValue, AllocValue, FrozenHeap,
    FrozenValue, Heap, StarlarkValue, UnpackValue, Value,
};
use std::{
    cmp::Ordering,
    fmt::{self, Display, Write},
};

/// The result of calling `type()` on integers.
pub const INT_TYPE: &str = "int";

impl<'v> AllocValue<'v> for i32 {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        Value::new_int(self)
    }
}
impl AllocFrozenValue for i32 {
    fn alloc_frozen_value(self, _heap: &FrozenHeap) -> FrozenValue {
        FrozenValue::new_int(self)
    }
}

impl UnpackValue<'_> for i32 {
    fn unpack_value(value: Value) -> Option<Self> {
        value.unpack_int()
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
        None => ValueError::unsupported_owned(INT_TYPE, op, Some(INT_TYPE)),
    }
}

impl Display for PointerI32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

/// Define the int type
impl<'v> StarlarkValue<'v> for PointerI32 {
    starlark_type!(INT_TYPE);

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        Ok(match other.unpack_num() {
            Some(Num::Int(other)) => self.get() == other,
            Some(Num::Float(other)) => self.get() as f64 == other,
            None => false,
        })
    }

    fn collect_repr(&self, s: &mut String) {
        write!(s, "{}", self).unwrap()
    }

    fn to_json(&self) -> anyhow::Result<String> {
        Ok(self.get().to_string())
    }
    fn to_int(&self) -> anyhow::Result<i32> {
        Ok(self.get())
    }
    fn to_bool(&self) -> bool {
        self.get() != 0
    }
    fn get_hash(&self) -> anyhow::Result<u64> {
        Ok(Num::from(self.get()).get_hash())
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
    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_num() {
            Some(Num::Int(other)) => self
                .get()
                .checked_add(other)
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into()),
            Some(Num::Float(_)) => (self.get() as f64).add(other, heap),
            None => ValueError::unsupported_with(self, "+", other),
        }
    }
    fn sub(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_num() {
            Some(Num::Int(other)) => self
                .get()
                .checked_sub(other)
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into()),
            Some(Num::Float(_)) => (self.get() as f64).sub(other, heap),
            None => ValueError::unsupported_with(self, "-", other),
        }
    }
    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            self.get()
                .checked_mul(other)
                .ok_or_else(|| ValueError::IntegerOverflow.into())
                .map(Value::new_int)
        } else {
            other.mul(Value::new_int(self.get()), heap)
        }
    }
    fn div(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if other.unpack_num().is_some() {
            (self.get() as f64).div(other, heap)
        } else {
            ValueError::unsupported_with(self, "/", other)
        }
    }
    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(Num::Float(_)) = other.unpack_num() {
            return (self.get() as f64).percent(other, heap);
        }
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
    fn floor_div(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(Num::Float(_)) = other.unpack_num() {
            return (self.get() as f64).floor_div(other, heap);
        }
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

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        match other.unpack_num() {
            Some(Num::Int(other)) => Ok(self.get().cmp(&other)),
            Some(Num::Float(_)) => (self.get() as f64).compare(other),
            None => ValueError::unsupported_with(self, "==", other),
        }
    }

    fn bit_and(&self, other: Value) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            Ok(Value::new_int(self.get() & other))
        } else {
            ValueError::unsupported_with(self, "&", other)
        }
    }

    fn bit_or(&self, other: Value) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            Ok(Value::new_int(self.get() | other))
        } else {
            ValueError::unsupported_with(self, "|", other)
        }
    }

    fn bit_xor(&self, other: Value) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            Ok(Value::new_int(self.get() ^ other))
        } else {
            ValueError::unsupported_with(self, "^", other)
        }
    }

    fn left_shift(&self, other: Value) -> anyhow::Result<Value<'v>> {
        use std::convert::TryInto;
        if let Some(other) = other.unpack_int() {
            other
                .try_into()
                .ok()
                .and_then(|unsigned_other| self.get().checked_shl(unsigned_other))
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into())
        } else {
            ValueError::unsupported_with(self, "<<", other)
        }
    }

    fn right_shift(&self, other: Value) -> anyhow::Result<Value<'v>> {
        use std::convert::TryInto;
        if let Some(other) = other.unpack_int() {
            other
                .try_into()
                .ok()
                .and_then(|unsigned_other| self.get().checked_shr(unsigned_other))
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into())
        } else {
            ValueError::unsupported_with(self, ">>", other)
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
1 + 2.0 == 3.0
1 - 2 == -1
1 - 2.0 == -1.0
2 * 3 == 6
2 * 3.0 == 6.0
4 / 2 == 2.0
5 % 3 == 2
4 // 2 == 2
"#,
        );
    }
}
