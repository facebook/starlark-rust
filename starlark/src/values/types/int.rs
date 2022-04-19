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

use std::{
    cmp::Ordering,
    fmt::{self, Debug, Display},
    hash::Hasher,
};

use gazebo::{any::AnyLifetime, cast};
use serde::{Serialize, Serializer};

use crate::{
    collections::{StarlarkHashValue, StarlarkHasher},
    values::{
        basic::StarlarkValueBasic, error::ValueError, float::StarlarkFloat, num::Num,
        AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, StarlarkValue, UnpackValue,
        Value,
    },
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
    fn expected() -> String {
        "int".to_owned()
    }

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

// WARNING: This type isn't a real type, a pointer to this is secretly an i32.
// Therefore, don't derive stuff on it, since it will be wrong.
// However, `AnyLifetime` promises not to peek at its value, so that's fine.
#[derive(AnyLifetime)]
#[repr(C)]
pub(crate) struct PointerI32 {
    _private: (),
}

impl Debug for PointerI32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.get(), f)
    }
}

impl PointerI32 {
    const TAG: usize = 0x100000000;

    pub(crate) fn new(x: i32) -> &'static Self {
        // UB if the pointer isn't aligned, or it is zero
        // Alignment is 1, so that's not an issue.
        // To deal with 0's we OR in TAG.
        unsafe { cast::usize_to_ptr(x as usize | Self::TAG) }
    }

    pub(crate) fn get(&self) -> i32 {
        cast::ptr_to_usize(self) as i32
    }

    pub(crate) fn type_is_pointer_i32<'v, T: StarlarkValue<'v>>() -> bool {
        T::static_type_id() == PointerI32::static_type_id()
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

    fn is_special() -> bool
    where
        Self: Sized,
    {
        true
    }

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        Ok(match other.unpack_num() {
            Some(Num::Int(other)) => self.get() == other,
            Some(Num::Float(other)) => self.get() as f64 == other,
            None => false,
        })
    }

    fn to_int(&self) -> anyhow::Result<i32> {
        Ok(self.get())
    }
    fn to_bool(&self) -> bool {
        self.get() != 0
    }
    fn write_hash(&self, hasher: &mut StarlarkHasher) -> anyhow::Result<()> {
        hasher.write_u64(Num::from(self.get()).get_hash_64());
        Ok(())
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
    fn add(&self, other: Value<'v>, heap: &'v Heap) -> Option<anyhow::Result<Value<'v>>> {
        match other.unpack_num() {
            Some(Num::Int(other)) => Some(
                self.get()
                    .checked_add(other)
                    .map(Value::new_int)
                    .ok_or_else(|| ValueError::IntegerOverflow.into()),
            ),
            Some(Num::Float(_)) => StarlarkFloat(self.get() as f64).add(other, heap),
            None => None,
        }
    }
    fn sub(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_num() {
            Some(Num::Int(other)) => self
                .get()
                .checked_sub(other)
                .map(Value::new_int)
                .ok_or_else(|| ValueError::IntegerOverflow.into()),
            Some(Num::Float(_)) => StarlarkFloat(self.get() as f64).sub(other, heap),
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
            StarlarkFloat(self.get() as f64).div(other, heap)
        } else {
            ValueError::unsupported_with(self, "/", other)
        }
    }
    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(Num::Float(_)) = other.unpack_num() {
            return StarlarkFloat(self.get() as f64).percent(other, heap);
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
            return StarlarkFloat(self.get() as f64).floor_div(other, heap);
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
            Some(Num::Float(_)) => StarlarkFloat(self.get() as f64).compare(other),
            None => ValueError::unsupported_with(self, "==", other),
        }
    }

    fn bit_and(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            Ok(Value::new_int(self.get() & other))
        } else {
            ValueError::unsupported_with(self, "&", other)
        }
    }

    fn bit_or(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            Ok(Value::new_int(self.get() | other))
        } else {
            ValueError::unsupported_with(self, "|", other)
        }
    }

    fn bit_xor(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            Ok(Value::new_int(self.get() ^ other))
        } else {
            ValueError::unsupported_with(self, "^", other)
        }
    }

    fn bit_not(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(Value::new_int(!self.get()))
    }

    fn left_shift(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            if let Ok(other) = other.try_into() {
                if let Some(r) = self.get().checked_shl(other) {
                    Ok(Value::new_int(r))
                } else {
                    Err(ValueError::IntegerOverflow.into())
                }
            } else {
                Err(ValueError::NegativeShiftCount.into())
            }
        } else {
            ValueError::unsupported_with(self, "<<", other)
        }
    }

    fn right_shift(&self, other: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_int() {
            if let Ok(other) = other.try_into() {
                if let Some(r) = self.get().checked_shr(other) {
                    Ok(Value::new_int(r))
                } else {
                    Err(ValueError::IntegerOverflow.into())
                }
            } else {
                Err(ValueError::NegativeShiftCount.into())
            }
        } else {
            ValueError::unsupported_with(self, ">>", other)
        }
    }
}

impl<'v> StarlarkValueBasic<'v> for PointerI32 {
    fn get_hash(&self) -> StarlarkHashValue {
        Num::from(self.get()).get_hash()
    }
}

impl Serialize for PointerI32 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_i32(self.get())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

    #[test]
    fn test_int_tag() {
        fn check(x: i32) {
            assert_eq!(x, PointerI32::new(x).get())
        }

        for x in -10..10 {
            check(x)
        }
        check(i32::MAX);
        check(i32::MIN);
    }

    #[test]
    fn test_alignment_int_pointer() {
        assert_eq!(1, std::mem::align_of::<PointerI32>());
    }
}
