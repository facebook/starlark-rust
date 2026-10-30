/*
 * Copyright 2018 The Starlark in Rust Authors.
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

use std::cmp::Ordering;
use std::ops::Add;
use std::ops::Mul;
use std::ops::Sub;

use dupe::Dupe;
use num_bigint::BigInt;
use num_traits::FromPrimitive;

use crate as starlark;
use crate::collections::StarlarkHashValue;
use crate::values::AllocFrozenValue;
use crate::values::AllocValue;
use crate::values::UnpackValue;
use crate::values::type_repr::StarlarkTypeRepr;
use crate::values::types::float::StarlarkFloat;
use crate::values::types::int::int_or_big::StarlarkInt;
use crate::values::types::int::int_or_big::StarlarkIntRef;

#[derive(Debug, thiserror::Error)]
enum NumError {
    #[error("float division by zero: {0} / {1}")]
    DivisionByZero(Num, Num),
    #[error("int too large to convert to float")]
    IntTooLargeForFloat,
}

/// [`NumRef`] represents a numerical value that can be unpacked from a [`Value`].
///
/// It's an intermediate representation that facilitates conversions between
/// numerical types and helps in implementation of arithmetical operations
/// between them.
#[derive(Clone, Debug, Dupe, Copy, StarlarkTypeRepr, UnpackValue)]
#[doc(hidden)]
pub enum NumRef<'v> {
    Int(StarlarkIntRef<'v>),
    // `StarlarkFloat` not `f64` here because `f64` unpacks from `int` too.
    Float(StarlarkFloat),
}

#[derive(
    Debug,
    derive_more::Display,
    StarlarkTypeRepr,
    AllocValue,
    AllocFrozenValue
)]
#[doc(hidden)]
pub enum Num {
    Int(StarlarkInt),
    Float(f64),
}

impl<'v> NumRef<'v> {
    /// Get underlying value as float
    pub(crate) fn as_float(&self) -> f64 {
        match self {
            Self::Int(i) => i.to_f64(),
            Self::Float(f) => f.0,
        }
    }

    /// Get underlying value as float, failing if it is an int too large to be
    /// represented as a finite float.
    pub(crate) fn as_finite_float(&self) -> anyhow::Result<f64> {
        let f = self.as_float();
        if f.is_infinite() && matches!(self, Self::Int(_)) {
            return Err(NumError::IntTooLargeForFloat.into());
        }
        Ok(f)
    }

    pub(crate) fn f64_to_i32_exact(f: f64) -> Option<i32> {
        let i = f as i32;
        if i as f64 == f { Some(i) } else { None }
    }

    /// Get underlying value as int (if it can be precisely expressed as int)
    pub(crate) fn as_int(&self) -> Option<i32> {
        match self {
            Self::Int(i) => i.to_i32(),
            Self::Float(f) => Self::f64_to_i32_exact(f.0),
        }
    }

    /// Compare an int with a float exactly, as the spec requires, rather than
    /// rounding the int to a float first.
    fn cmp_int_float(i: StarlarkIntRef, f: f64) -> Ordering {
        match i {
            // An `i32` converts to `f64` exactly, so comparing the floats is exact.
            StarlarkIntRef::Small(i) => StarlarkFloat::compare_impl(i.to_f64(), f),
            StarlarkIntRef::Big(b) => {
                if !f.is_finite() {
                    // Every int is above `-inf` and below `+inf` and NaN.
                    return StarlarkFloat::compare_impl(0.0, f);
                }
                let floor = f.floor();
                // `floor` is finite and integral, so the conversion is exact.
                let floor_int = BigInt::from_f64(floor).expect("finite float converts to BigInt");
                match b.get().cmp(&floor_int) {
                    // `floor < f`, so an int equal to `floor` is below `f`.
                    Ordering::Equal if floor != f => Ordering::Less,
                    ord => ord,
                }
            }
        }
    }

    /// Get hash of the underlying number
    pub(crate) fn get_hash_64(self) -> u64 {
        fn float_hash(f: f64) -> u64 {
            if f.is_nan() {
                // all possible NaNs should hash to the same value
                0
            } else if f.is_infinite() {
                u64::MAX
            } else if f == 0.0 {
                // Both 0.0 and -0.0 need the same hash, but are both equal to 0.0
                0.0f64.to_bits()
            } else {
                f.to_bits()
            }
        }

        match (self.as_int(), self) {
            // equal ints and floats should have the same hash
            (Some(i), _) => i as u64,
            (None, Self::Float(f)) => float_hash(f.0),
            (None, Self::Int(StarlarkIntRef::Small(i))) => {
                // shouldn't happen - as_int() should have resulted in an int
                i.to_i32() as u64
            }
            (None, Self::Int(StarlarkIntRef::Big(b))) => {
                // Not perfect, but OK: `1000000000000000000000003` and `1000000000000000000000005`
                // flush to the same float, and neither is exact float,
                // so we could use better hash for such numbers.
                float_hash(b.to_f64())
            }
        }
    }

    pub(crate) fn get_hash(self) -> StarlarkHashValue {
        StarlarkHashValue::hash_64(self.get_hash_64())
    }

    fn to_owned(self) -> Num {
        match self {
            NumRef::Int(i) => Num::Int(i.to_owned()),
            NumRef::Float(f) => Num::Float(f.0),
        }
    }

    pub(crate) fn div(self, other: NumRef) -> anyhow::Result<f64> {
        let a = self.as_finite_float()?;
        let b = other.as_finite_float()?;
        if b == 0.0 {
            Err(NumError::DivisionByZero(self.to_owned(), other.to_owned()).into())
        } else {
            Ok(a / b)
        }
    }

    pub(crate) fn floor_div(self, other: NumRef) -> anyhow::Result<Num> {
        if let (NumRef::Int(a), NumRef::Int(b)) = (self, other) {
            a.floor_div(b).map(Num::Int)
        } else {
            StarlarkFloat::floor_div_impl(self.as_finite_float()?, other.as_finite_float()?)
                .map(Num::Float)
        }
    }

    pub(crate) fn percent(self, other: NumRef) -> anyhow::Result<Num> {
        if let (NumRef::Int(a), NumRef::Int(b)) = (self, other) {
            a.percent(b).map(Num::Int)
        } else {
            StarlarkFloat::percent_impl(self.as_finite_float()?, other.as_finite_float()?)
                .map(Num::Float)
        }
    }
}

impl<'v> From<f64> for NumRef<'v> {
    fn from(f: f64) -> Self {
        Self::Float(StarlarkFloat(f))
    }
}

/// This is total eq per starlark spec, not Rust's partial eq.
impl<'v> PartialEq for NumRef<'v> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<'v> Eq for NumRef<'v> {}

impl<'v> PartialOrd for NumRef<'v> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'v> Ord for NumRef<'v> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (NumRef::Int(a), NumRef::Int(b)) => a.cmp(b),
            (NumRef::Int(a), NumRef::Float(b)) => Self::cmp_int_float(*a, b.0),
            (NumRef::Float(a), NumRef::Int(b)) => Self::cmp_int_float(*b, a.0).reverse(),
            (NumRef::Float(a), NumRef::Float(b)) => StarlarkFloat::compare_impl(a.0, b.0),
        }
    }
}

impl<'v> Add for NumRef<'v> {
    type Output = anyhow::Result<Num>;

    fn add(self, rhs: Self) -> Self::Output {
        if let (NumRef::Int(a), NumRef::Int(b)) = (self, rhs) {
            return Ok(Num::Int(a + b));
        }
        Ok(Num::Float(self.as_finite_float()? + rhs.as_finite_float()?))
    }
}

impl<'v> Sub for NumRef<'v> {
    type Output = anyhow::Result<Num>;

    fn sub(self, rhs: Self) -> Self::Output {
        if let (NumRef::Int(a), NumRef::Int(b)) = (self, rhs) {
            return Ok(Num::Int(a - b));
        }
        Ok(Num::Float(self.as_finite_float()? - rhs.as_finite_float()?))
    }
}

impl<'v> Mul for NumRef<'v> {
    type Output = anyhow::Result<Num>;

    fn mul(self, rhs: Self) -> Self::Output {
        if let (NumRef::Int(a), NumRef::Int(b)) = (self, rhs) {
            return Ok(Num::Int(a * b));
        }
        Ok(Num::Float(self.as_finite_float()? * rhs.as_finite_float()?))
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;
    use crate::values::Value;
    use crate::values::types::int::inline_int::InlineInt;

    #[test]
    fn test_from_value() {
        assert!(
            NumRef::unpack_value(Value::new_bool(true))
                .unwrap()
                .is_none()
        );
        assert!(
            NumRef::unpack_value(Value::new_bool(false))
                .unwrap()
                .is_none()
        );
        assert!(
            NumRef::unpack_value(Value::new_empty_string())
                .unwrap()
                .is_none()
        );
        assert!(NumRef::unpack_value(Value::new_none()).unwrap().is_none());

        assert_eq!(
            NumRef::unpack_value(Value::testing_new_int(0))
                .unwrap()
                .unwrap()
                .as_int(),
            Some(0)
        );
        assert_eq!(
            NumRef::unpack_value(Value::testing_new_int(42))
                .unwrap()
                .unwrap()
                .as_int(),
            Some(42)
        );
        assert_eq!(
            NumRef::unpack_value(Value::testing_new_int(-42))
                .unwrap()
                .unwrap()
                .as_int(),
            Some(-42)
        );
    }

    #[test]
    fn test_conversion_to_float() {
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::ZERO)).as_float(),
            0.0
        );
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::MAX)).as_float(),
            InlineInt::MAX.to_f64()
        );
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::MIN)).as_float(),
            InlineInt::MIN.to_f64()
        );

        assert_eq!(NumRef::Float(StarlarkFloat(0.0)).as_float(), 0.0);
        assert!(NumRef::Float(StarlarkFloat(f64::NAN)).as_float().is_nan());
    }

    #[test]
    fn test_conversion_to_int() {
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::testing_new(0))).as_int(),
            Some(0)
        );
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::testing_new(42))).as_int(),
            Some(42)
        );
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::testing_new(-42))).as_int(),
            Some(-42)
        );

        assert_eq!(NumRef::Float(StarlarkFloat(0_f64)).as_int(), Some(0));
        assert_eq!(NumRef::Float(StarlarkFloat(42_f64)).as_int(), Some(42));
        assert_eq!(NumRef::Float(StarlarkFloat(-42_f64)).as_int(), Some(-42));

        assert_eq!(
            NumRef::Float(StarlarkFloat(i32::MIN as f64)).as_int(),
            Some(i32::MIN)
        );
        assert_eq!(
            NumRef::Float(StarlarkFloat(i32::MAX as f64)).as_int(),
            Some(i32::MAX)
        );

        assert_eq!(NumRef::Float(StarlarkFloat(42.75)).as_int(), None);
        assert_eq!(NumRef::Float(StarlarkFloat(-42.75)).as_int(), None);
        assert_eq!(NumRef::Float(StarlarkFloat(f64::NAN)).as_int(), None);
        assert_eq!(NumRef::Float(StarlarkFloat(f64::INFINITY)).as_int(), None);
        assert_eq!(
            NumRef::Float(StarlarkFloat(f64::NEG_INFINITY)).as_int(),
            None
        );
    }

    #[test]
    fn test_hashing() {
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::testing_new(0))).get_hash_64(),
            NumRef::Float(StarlarkFloat(0.0)).get_hash_64()
        );
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::testing_new(42))).get_hash_64(),
            NumRef::Float(StarlarkFloat(42.0)).get_hash_64()
        );

        assert_eq!(
            NumRef::Float(StarlarkFloat(f64::INFINITY + f64::NEG_INFINITY)).get_hash_64(),
            NumRef::Float(StarlarkFloat(f64::NAN)).get_hash_64()
        );
        assert_eq!(
            NumRef::Float(StarlarkFloat("0.25".parse().unwrap())).get_hash_64(),
            NumRef::Float(StarlarkFloat("25e-2".parse().unwrap())).get_hash_64()
        );

        let x = 1u64 << 55;
        assert_eq!(x as f64 as u64, x, "Self-check");
        assert_eq!(
            NumRef::Float(StarlarkFloat(x as f64)).get_hash_64(),
            NumRef::Int(StarlarkInt::from(BigInt::from(x)).as_ref()).get_hash_64(),
        )
    }

    #[test]
    fn test_eq() {
        assert_eq!(
            NumRef::Float(StarlarkFloat(f64::NAN)),
            NumRef::Float(StarlarkFloat(f64::NAN))
        );
        assert_eq!(
            NumRef::Float(StarlarkFloat(f64::INFINITY)),
            NumRef::Float(StarlarkFloat(f64::INFINITY))
        );
        assert_eq!(
            NumRef::Int(StarlarkIntRef::Small(InlineInt::testing_new(10))),
            NumRef::Float(StarlarkFloat(10.0))
        );
    }

    #[test]
    fn test_cmp_int_float_exact() {
        fn big(i: i128) -> StarlarkInt {
            StarlarkInt::from(BigInt::from(i))
        }
        let p53 = 1i128 << 53;
        // `p53 + 1` rounds to `p53` as a float, but is not equal to it.
        assert_eq!(
            NumRef::Int(big(p53 + 1).as_ref()).cmp(&NumRef::Float(StarlarkFloat(p53 as f64))),
            Ordering::Greater
        );
        assert_eq!(
            NumRef::Float(StarlarkFloat(p53 as f64)).cmp(&NumRef::Int(big(p53 + 1).as_ref())),
            Ordering::Less
        );
        assert_eq!(
            NumRef::Int(big(p53).as_ref()),
            NumRef::Float(StarlarkFloat(p53 as f64))
        );
        assert_eq!(
            NumRef::Int(big(-p53 - 1).as_ref()).cmp(&NumRef::Float(StarlarkFloat(-(p53 as f64)))),
            Ordering::Less
        );
        // A fraction puts the float strictly between two ints.
        assert_eq!(
            NumRef::Int(big(p53).as_ref()).cmp(&NumRef::Float(StarlarkFloat(1e15 + 0.5))),
            Ordering::Greater
        );
        assert_eq!(
            NumRef::Int(big(-p53).as_ref()).cmp(&NumRef::Float(StarlarkFloat(-1e15 - 0.5))),
            Ordering::Less
        );
        // No int is equal to a non-finite float.
        let huge = big(1 << 100);
        let huge = huge.as_ref();
        assert_eq!(
            NumRef::Int(huge).cmp(&NumRef::Float(StarlarkFloat(f64::INFINITY))),
            Ordering::Less
        );
        assert_eq!(
            NumRef::Int(huge).cmp(&NumRef::Float(StarlarkFloat(f64::NEG_INFINITY))),
            Ordering::Greater
        );
        assert_eq!(
            NumRef::Int(huge).cmp(&NumRef::Float(StarlarkFloat(f64::NAN))),
            Ordering::Less
        );
    }
}
