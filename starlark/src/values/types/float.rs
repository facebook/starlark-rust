/*
 * Copyright 2021 The Starlark in Rust Authors.
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

//! The floating point number type (3.14, 4e2).

use std::cmp::Ordering;

use crate::values::{AllocFrozenValue, FrozenHeap, FrozenValue, Heap, SimpleValue, StarlarkValue, Value, ValueError};

/// The result of calling `type()` on integers.
pub const FLOAT_TYPE: &str = "float";

impl AllocFrozenValue for f64 {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(self)
    }
}

impl SimpleValue for f64 {}


impl<'v> StarlarkValue<'v> for f64 {
    starlark_type!(FLOAT_TYPE);

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        if let Some(other) = other.unpack_and_coerce_float() {
            Ok(*self == other)
        } else {
            Ok(false)
        }
    }

    fn collect_repr(&self, s: &mut String) {
        s.push_str(&self.to_string());
    }

    fn to_json(&self) -> anyhow::Result<String> {
        Ok(self.to_string())
    }

    fn to_int(&self) -> anyhow::Result<i32> {
        let candidate = self.trunc();
        if i32::MIN as f64 <= candidate && candidate <= i32::MAX as f64 {
            Ok(self.trunc() as i32)
        } else {
            Err(ValueError::IntegerOverflow.into())
        }
    }

    fn to_bool(&self) -> bool {
        *self != 0.0
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        Ok(self.to_bits())
    }

    fn plus(&self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(heap.alloc_simple(*self))
    }

    fn minus(&self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(heap.alloc_simple(-*self))
    }

    fn add(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_and_coerce_float() {
            Ok(heap.alloc_simple(*self + other))
        } else {
            ValueError::unsupported_with(self, "+", other)
        }
    }

    fn sub(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_and_coerce_float() {
            Ok(heap.alloc_simple(*self - other))
        } else {
            ValueError::unsupported_with(self, "-", other)
        }
    }

    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_and_coerce_float() {
            Ok(heap.alloc_simple(*self * other))
        } else {
            ValueError::unsupported_with(self, "*", other)
        }
    }

    fn div(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_and_coerce_float() {
            if other == 0.0 {
                return Err(ValueError::DivisionByZero.into());
            }
            Ok(heap.alloc_simple(*self / other))
        } else {
            ValueError::unsupported_with(self, "%", other)
        }
    }

    fn percent(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_and_coerce_float() {
            if other == 0.0 {
                return Err(ValueError::DivisionByZero.into());
            }
            Ok(heap.alloc_simple(*self % other))
        } else {
            ValueError::unsupported_with(self, "%", other)
        }
    }

    fn floor_div(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = other.unpack_and_coerce_float() {
            if other == 0.0 {
                return Err(ValueError::DivisionByZero.into());
            }
            Ok(heap.alloc_simple((*self / other).trunc()))
        } else {
            ValueError::unsupported_with(self, "%", other)
        }
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        if let Some(other_float) = other.unpack_and_coerce_float() {
            // According to the spec (https://github.com/bazelbuild/starlark/blob/689f54426951638ef5b7c41a14d8fc48e65c5f77/spec.md#floating-point-numbers)
            // All NaN values compare equal to each other, but greater than any non-NaN float value.
            match (self.is_nan(), other_float.is_nan()) {
                (true, true) => Ok(Ordering::Equal),
                (true, false) => Ok(Ordering::Greater),
                (false, true) => Ok(Ordering::Less),
                (false, false) => if let Some(ordering) = self.partial_cmp(&other_float) {
                    Ok(ordering)
                } else {
                    // This shouldn't happen as we handle potential NaNs above
                    ValueError::unsupported_with(self, "==", other)
                }
            }
        } else {
            ValueError::unsupported_with(self, "==", other)
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
+1.0 == 1.0
-1.0 == 0. - 1.
1.0 + 2.0 == 3.0
1.0 - 2.0 == -1.0
2.0 * 3.0 == 6.0
5.0 % 3.0 == 2.0
"#,
        );
    }
}
