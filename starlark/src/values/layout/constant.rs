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
    ptr,
};

/// A constant string that can be converted to a [`FrozenValue`].
#[repr(C)] // Must match this layout on the heap
pub struct StarlarkStrN<const N: usize> {
    repr: AValueRepr<StarlarkStr>,
    payload: [u8; N],
}

impl<const N: usize> StarlarkStrN<N> {
    /// Create a new [`StarlarkStrN`] given a string of size `N`.
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

    /// Obtain the [`FrozenValue`] for a [`StarlarkStrN`].
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
unsafe impl<'v> Coerce<Value<'v>> for StringValue<'v> {}
unsafe impl<'v> CoerceKey<Value<'v>> for StringValue<'v> {}

impl PartialEq for FrozenStringValue {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other) || self.as_str() == other.as_str()
    }
}

impl Eq for FrozenStringValue {}

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

    /// Construct from a value. Returns [`None`] if a value does not contain a string.
    pub(crate) fn new(value: FrozenValue) -> Option<FrozenStringValue> {
        if value.unpack_str().is_some() {
            Some(unsafe { Self::new_unchecked(value) })
        } else {
            None
        }
    }

    /// Get a string.
    pub(crate) fn as_str(self) -> &'static str {
        self.0.payload.unpack()
    }
}

impl<'v> PartialEq for StringValue<'v> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(other.0) || self.as_str() == other.as_str()
    }
}

impl<'v> Eq for StringValue<'v> {}

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

    pub(crate) fn as_str(self) -> &'v str {
        self.unpack_starlark_str().unpack()
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
        static X: starlark::values::StarlarkStrN<N> = starlark::values::StarlarkStrN::new($s);
        X.erase()
    }};
}

pub(crate) static VALUE_EMPTY_STRING: StarlarkStrN<0> = StarlarkStrN::new("");

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

pub(crate) static VALUE_BYTE_STRINGS: [StarlarkStrN<1>; 128] = [
    StarlarkStrN::new("\x00"),
    StarlarkStrN::new("\x01"),
    StarlarkStrN::new("\x02"),
    StarlarkStrN::new("\x03"),
    StarlarkStrN::new("\x04"),
    StarlarkStrN::new("\x05"),
    StarlarkStrN::new("\x06"),
    StarlarkStrN::new("\x07"),
    StarlarkStrN::new("\x08"),
    StarlarkStrN::new("\x09"),
    StarlarkStrN::new("\x0A"),
    StarlarkStrN::new("\x0B"),
    StarlarkStrN::new("\x0C"),
    StarlarkStrN::new("\x0D"),
    StarlarkStrN::new("\x0E"),
    StarlarkStrN::new("\x0F"),
    StarlarkStrN::new("\x10"),
    StarlarkStrN::new("\x11"),
    StarlarkStrN::new("\x12"),
    StarlarkStrN::new("\x13"),
    StarlarkStrN::new("\x14"),
    StarlarkStrN::new("\x15"),
    StarlarkStrN::new("\x16"),
    StarlarkStrN::new("\x17"),
    StarlarkStrN::new("\x18"),
    StarlarkStrN::new("\x19"),
    StarlarkStrN::new("\x1A"),
    StarlarkStrN::new("\x1B"),
    StarlarkStrN::new("\x1C"),
    StarlarkStrN::new("\x1D"),
    StarlarkStrN::new("\x1E"),
    StarlarkStrN::new("\x1F"),
    StarlarkStrN::new("\x20"),
    StarlarkStrN::new("\x21"),
    StarlarkStrN::new("\x22"),
    StarlarkStrN::new("\x23"),
    StarlarkStrN::new("\x24"),
    StarlarkStrN::new("\x25"),
    StarlarkStrN::new("\x26"),
    StarlarkStrN::new("\x27"),
    StarlarkStrN::new("\x28"),
    StarlarkStrN::new("\x29"),
    StarlarkStrN::new("\x2A"),
    StarlarkStrN::new("\x2B"),
    StarlarkStrN::new("\x2C"),
    StarlarkStrN::new("\x2D"),
    StarlarkStrN::new("\x2E"),
    StarlarkStrN::new("\x2F"),
    StarlarkStrN::new("\x30"),
    StarlarkStrN::new("\x31"),
    StarlarkStrN::new("\x32"),
    StarlarkStrN::new("\x33"),
    StarlarkStrN::new("\x34"),
    StarlarkStrN::new("\x35"),
    StarlarkStrN::new("\x36"),
    StarlarkStrN::new("\x37"),
    StarlarkStrN::new("\x38"),
    StarlarkStrN::new("\x39"),
    StarlarkStrN::new("\x3A"),
    StarlarkStrN::new("\x3B"),
    StarlarkStrN::new("\x3C"),
    StarlarkStrN::new("\x3D"),
    StarlarkStrN::new("\x3E"),
    StarlarkStrN::new("\x3F"),
    StarlarkStrN::new("\x40"),
    StarlarkStrN::new("\x41"),
    StarlarkStrN::new("\x42"),
    StarlarkStrN::new("\x43"),
    StarlarkStrN::new("\x44"),
    StarlarkStrN::new("\x45"),
    StarlarkStrN::new("\x46"),
    StarlarkStrN::new("\x47"),
    StarlarkStrN::new("\x48"),
    StarlarkStrN::new("\x49"),
    StarlarkStrN::new("\x4A"),
    StarlarkStrN::new("\x4B"),
    StarlarkStrN::new("\x4C"),
    StarlarkStrN::new("\x4D"),
    StarlarkStrN::new("\x4E"),
    StarlarkStrN::new("\x4F"),
    StarlarkStrN::new("\x50"),
    StarlarkStrN::new("\x51"),
    StarlarkStrN::new("\x52"),
    StarlarkStrN::new("\x53"),
    StarlarkStrN::new("\x54"),
    StarlarkStrN::new("\x55"),
    StarlarkStrN::new("\x56"),
    StarlarkStrN::new("\x57"),
    StarlarkStrN::new("\x58"),
    StarlarkStrN::new("\x59"),
    StarlarkStrN::new("\x5A"),
    StarlarkStrN::new("\x5B"),
    StarlarkStrN::new("\x5C"),
    StarlarkStrN::new("\x5D"),
    StarlarkStrN::new("\x5E"),
    StarlarkStrN::new("\x5F"),
    StarlarkStrN::new("\x60"),
    StarlarkStrN::new("\x61"),
    StarlarkStrN::new("\x62"),
    StarlarkStrN::new("\x63"),
    StarlarkStrN::new("\x64"),
    StarlarkStrN::new("\x65"),
    StarlarkStrN::new("\x66"),
    StarlarkStrN::new("\x67"),
    StarlarkStrN::new("\x68"),
    StarlarkStrN::new("\x69"),
    StarlarkStrN::new("\x6A"),
    StarlarkStrN::new("\x6B"),
    StarlarkStrN::new("\x6C"),
    StarlarkStrN::new("\x6D"),
    StarlarkStrN::new("\x6E"),
    StarlarkStrN::new("\x6F"),
    StarlarkStrN::new("\x70"),
    StarlarkStrN::new("\x71"),
    StarlarkStrN::new("\x72"),
    StarlarkStrN::new("\x73"),
    StarlarkStrN::new("\x74"),
    StarlarkStrN::new("\x75"),
    StarlarkStrN::new("\x76"),
    StarlarkStrN::new("\x77"),
    StarlarkStrN::new("\x78"),
    StarlarkStrN::new("\x79"),
    StarlarkStrN::new("\x7A"),
    StarlarkStrN::new("\x7B"),
    StarlarkStrN::new("\x7C"),
    StarlarkStrN::new("\x7D"),
    StarlarkStrN::new("\x7E"),
    StarlarkStrN::new("\x7F"),
];
