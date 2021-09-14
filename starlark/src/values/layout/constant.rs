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

use crate::values::{
    layout::{arena::AValueRepr, avalue::VALUE_STR_A_VALUE_PTR, value::FrozenValue},
    string::StarlarkStr,
    Freezer, Trace, Tracer, Value,
};
use gazebo::{
    coerce::{Coerce, CoerceKey},
    prelude::*,
};
use std::{
    fmt,
    fmt::{Debug, Formatter},
    intrinsics::copy_nonoverlapping,
};

/// A constant string that can be converted to a [`FrozenValue`].
#[repr(C)] // Must match this layout on the heap
pub struct ConstFrozenStringN<const N: usize> {
    repr: AValueRepr<StarlarkStr>,
    payload: [u8; N],
}

impl<const N: usize> ConstFrozenStringN<N> {
    /// Create a new [`ConstFrozenStringN`] given a string of size `N`.
    /// If the string has a different size it will fail.
    pub const fn new(s: &str) -> Self {
        assert!(N == s.len());
        let mut payload = [0u8; N];
        unsafe {
            copy_nonoverlapping(s.as_ptr(), payload.as_mut_ptr(), N)
        };
        Self {
            repr: AValueRepr {
                header: VALUE_STR_A_VALUE_PTR,
                payload: unsafe { StarlarkStr::new(N) },
            },
            payload,
        }
    }

    /// Obtain the [`FrozenValue`] for a [`ConstFrozenStringN`].
    pub fn unpack(&'static self) -> FrozenValue {
        self.erase().unpack()
    }

    /// Erase the type parameter, giving a slightly nicer user experience.
    pub const fn erase(&'static self) -> FrozenStringValue {
        FrozenStringValue(&self.repr)
    }
}

/// Define a `&'static` [`str`] that can be converted to a [`FrozenValue`].
///
/// Usually used as:
///
/// ```
/// use starlark::const_frozen_string;
/// use starlark::values::{FrozenStringValue, FrozenValue};
///
/// static RES: FrozenStringValue = const_frozen_string!("magic");
/// let fv: FrozenValue = RES.unpack();
/// assert_eq!(Some("magic"), fv.to_value().unpack_str());
/// ```
#[derive(Copy, Clone, Dupe)]
#[repr(C)]
pub struct FrozenStringValue(&'static AValueRepr<StarlarkStr>);

impl Debug for FrozenStringValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FrozenStringValue")
            .field(&self.unpack())
            .finish()
    }
}

/// Wrapper for a [`Value`] which can only contain a [`StarlarkStr`].
#[derive(Copy, Clone, Dupe, Debug)]
#[repr(C)]
pub struct StringValue<'v>(Value<'v>);

unsafe impl<'v> Coerce<StringValue<'v>> for FrozenStringValue {}
unsafe impl<'v> CoerceKey<StringValue<'v>> for FrozenStringValue {}
unsafe impl<'v> Coerce<StringValue<'v>> for StringValue<'v> {}
unsafe impl<'v> CoerceKey<StringValue<'v>> for StringValue<'v> {}

impl FrozenStringValue {
    /// Obtain the [`FrozenValue`] for a [`FrozenStringValue`].
    pub fn unpack(self) -> FrozenValue {
        FrozenValue::new_repr(self.0)
    }

    /// Construct without a check that the value contains a string.
    ///
    /// If passed value does not contain a string, it may lead to memory corruption.
    pub(crate) unsafe fn new_unchecked(value: FrozenValue) -> FrozenStringValue {
        debug_assert!(value.unpack_str().is_some());
        FrozenStringValue(&*(value.0.ptr_value() as *const AValueRepr<StarlarkStr>))
    }
}

impl<'v> StringValue<'v> {
    /// Construct without a check that the value contains a string.
    ///
    /// If passed value does not contain a string, it may lead to memory corruption.
    pub(crate) unsafe fn new_unchecked(value: Value<'v>) -> StringValue<'v> {
        debug_assert!(value.unpack_str().is_some());
        StringValue(value)
    }

    /// Construct from a value. Returns [`None`] if a value does not contain a string.
    pub(crate) fn new(value: Value<'v>) -> Option<StringValue<'v>> {
        if value.unpack_str().is_some() {
            Some(StringValue(value))
        } else {
            None
        }
    }

    pub(crate) fn unpack_starlark_str(self) -> &'v StarlarkStr {
        debug_assert!(self.0.unpack_str().is_some());
        unsafe { &self.0.0.unpack_ptr_no_int_unchecked().as_repr().payload }
    }

    pub(crate) fn to_value(self) -> Value<'v> {
        self.0
    }

    /// Convert a value to a [`FrozenValue`] using a supplied [`Freezer`].
    pub(crate) fn freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenStringValue> {
        Ok(unsafe { FrozenStringValue::new_unchecked(freezer.freeze(self.0)?) })
    }
}

/// Common type for [`StringValue`] and [`FrozenStringValue`].
pub(crate) trait StringValueLike<'v>: Debug + Coerce<StringValue<'v>> {}

impl<'v> StringValueLike<'v> for StringValue<'v> {}

impl<'v> StringValueLike<'v> for FrozenStringValue {}

unsafe impl<'v> Trace<'v> for StringValue<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.0.trace(tracer);
        debug_assert!(self.0.unpack_str().is_some());
    }
}

/// Create a [`FrozenStringValue`].
#[macro_export]
macro_rules! const_frozen_string {
    ($s:expr) => {{
        const N: usize = $s.len();
        static X: starlark::values::ConstFrozenStringN<N> =
            starlark::values::ConstFrozenStringN::new($s);
        X.erase()
    }};
}

pub(crate) static VALUE_EMPTY_STRING: ConstFrozenStringN<0> = ConstFrozenStringN::new("");

#[inline(always)]
pub(crate) fn constant_string(x: &str) -> Option<FrozenValue> {
    if x.len() > 1 {
        None
    } else if x.is_empty() {
        Some(VALUE_EMPTY_STRING.unpack())
    } else {
        // If the string is 1 byte long there can only be up to the first 128 characters present
        // therefore this index will be total
        Some(VALUE_BYTE_STRINGS[x.as_bytes()[0] as usize].unpack())
    }
}

pub(crate) static VALUE_BYTE_STRINGS: [ConstFrozenStringN<1>; 128] = [
    ConstFrozenStringN::new("\x00"),
    ConstFrozenStringN::new("\x01"),
    ConstFrozenStringN::new("\x02"),
    ConstFrozenStringN::new("\x03"),
    ConstFrozenStringN::new("\x04"),
    ConstFrozenStringN::new("\x05"),
    ConstFrozenStringN::new("\x06"),
    ConstFrozenStringN::new("\x07"),
    ConstFrozenStringN::new("\x08"),
    ConstFrozenStringN::new("\x09"),
    ConstFrozenStringN::new("\x0A"),
    ConstFrozenStringN::new("\x0B"),
    ConstFrozenStringN::new("\x0C"),
    ConstFrozenStringN::new("\x0D"),
    ConstFrozenStringN::new("\x0E"),
    ConstFrozenStringN::new("\x0F"),
    ConstFrozenStringN::new("\x10"),
    ConstFrozenStringN::new("\x11"),
    ConstFrozenStringN::new("\x12"),
    ConstFrozenStringN::new("\x13"),
    ConstFrozenStringN::new("\x14"),
    ConstFrozenStringN::new("\x15"),
    ConstFrozenStringN::new("\x16"),
    ConstFrozenStringN::new("\x17"),
    ConstFrozenStringN::new("\x18"),
    ConstFrozenStringN::new("\x19"),
    ConstFrozenStringN::new("\x1A"),
    ConstFrozenStringN::new("\x1B"),
    ConstFrozenStringN::new("\x1C"),
    ConstFrozenStringN::new("\x1D"),
    ConstFrozenStringN::new("\x1E"),
    ConstFrozenStringN::new("\x1F"),
    ConstFrozenStringN::new("\x20"),
    ConstFrozenStringN::new("\x21"),
    ConstFrozenStringN::new("\x22"),
    ConstFrozenStringN::new("\x23"),
    ConstFrozenStringN::new("\x24"),
    ConstFrozenStringN::new("\x25"),
    ConstFrozenStringN::new("\x26"),
    ConstFrozenStringN::new("\x27"),
    ConstFrozenStringN::new("\x28"),
    ConstFrozenStringN::new("\x29"),
    ConstFrozenStringN::new("\x2A"),
    ConstFrozenStringN::new("\x2B"),
    ConstFrozenStringN::new("\x2C"),
    ConstFrozenStringN::new("\x2D"),
    ConstFrozenStringN::new("\x2E"),
    ConstFrozenStringN::new("\x2F"),
    ConstFrozenStringN::new("\x30"),
    ConstFrozenStringN::new("\x31"),
    ConstFrozenStringN::new("\x32"),
    ConstFrozenStringN::new("\x33"),
    ConstFrozenStringN::new("\x34"),
    ConstFrozenStringN::new("\x35"),
    ConstFrozenStringN::new("\x36"),
    ConstFrozenStringN::new("\x37"),
    ConstFrozenStringN::new("\x38"),
    ConstFrozenStringN::new("\x39"),
    ConstFrozenStringN::new("\x3A"),
    ConstFrozenStringN::new("\x3B"),
    ConstFrozenStringN::new("\x3C"),
    ConstFrozenStringN::new("\x3D"),
    ConstFrozenStringN::new("\x3E"),
    ConstFrozenStringN::new("\x3F"),
    ConstFrozenStringN::new("\x40"),
    ConstFrozenStringN::new("\x41"),
    ConstFrozenStringN::new("\x42"),
    ConstFrozenStringN::new("\x43"),
    ConstFrozenStringN::new("\x44"),
    ConstFrozenStringN::new("\x45"),
    ConstFrozenStringN::new("\x46"),
    ConstFrozenStringN::new("\x47"),
    ConstFrozenStringN::new("\x48"),
    ConstFrozenStringN::new("\x49"),
    ConstFrozenStringN::new("\x4A"),
    ConstFrozenStringN::new("\x4B"),
    ConstFrozenStringN::new("\x4C"),
    ConstFrozenStringN::new("\x4D"),
    ConstFrozenStringN::new("\x4E"),
    ConstFrozenStringN::new("\x4F"),
    ConstFrozenStringN::new("\x50"),
    ConstFrozenStringN::new("\x51"),
    ConstFrozenStringN::new("\x52"),
    ConstFrozenStringN::new("\x53"),
    ConstFrozenStringN::new("\x54"),
    ConstFrozenStringN::new("\x55"),
    ConstFrozenStringN::new("\x56"),
    ConstFrozenStringN::new("\x57"),
    ConstFrozenStringN::new("\x58"),
    ConstFrozenStringN::new("\x59"),
    ConstFrozenStringN::new("\x5A"),
    ConstFrozenStringN::new("\x5B"),
    ConstFrozenStringN::new("\x5C"),
    ConstFrozenStringN::new("\x5D"),
    ConstFrozenStringN::new("\x5E"),
    ConstFrozenStringN::new("\x5F"),
    ConstFrozenStringN::new("\x60"),
    ConstFrozenStringN::new("\x61"),
    ConstFrozenStringN::new("\x62"),
    ConstFrozenStringN::new("\x63"),
    ConstFrozenStringN::new("\x64"),
    ConstFrozenStringN::new("\x65"),
    ConstFrozenStringN::new("\x66"),
    ConstFrozenStringN::new("\x67"),
    ConstFrozenStringN::new("\x68"),
    ConstFrozenStringN::new("\x69"),
    ConstFrozenStringN::new("\x6A"),
    ConstFrozenStringN::new("\x6B"),
    ConstFrozenStringN::new("\x6C"),
    ConstFrozenStringN::new("\x6D"),
    ConstFrozenStringN::new("\x6E"),
    ConstFrozenStringN::new("\x6F"),
    ConstFrozenStringN::new("\x70"),
    ConstFrozenStringN::new("\x71"),
    ConstFrozenStringN::new("\x72"),
    ConstFrozenStringN::new("\x73"),
    ConstFrozenStringN::new("\x74"),
    ConstFrozenStringN::new("\x75"),
    ConstFrozenStringN::new("\x76"),
    ConstFrozenStringN::new("\x77"),
    ConstFrozenStringN::new("\x78"),
    ConstFrozenStringN::new("\x79"),
    ConstFrozenStringN::new("\x7A"),
    ConstFrozenStringN::new("\x7B"),
    ConstFrozenStringN::new("\x7C"),
    ConstFrozenStringN::new("\x7D"),
    ConstFrozenStringN::new("\x7E"),
    ConstFrozenStringN::new("\x7F"),
];
