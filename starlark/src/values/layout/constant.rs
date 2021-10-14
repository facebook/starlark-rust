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

use std::{
    borrow::Borrow,
    fmt,
    fmt::{Debug, Formatter},
    hash::{Hash, Hasher},
    intrinsics::copy_nonoverlapping,
    ops::Deref,
    ptr,
};

use gazebo::{
    coerce::{Coerce, CoerceKey},
    prelude::*,
};

use crate::values::{
    layout::{arena::AValueRepr, avalue::VALUE_STR_A_VALUE_PTR, value::FrozenValue},
    string::StarlarkStr,
    Freezer, Trace, Tracer, UnpackValue, Value,
};

/// A constant string that can be converted to a [`FrozenValue`].
#[repr(C)] // Must match this layout on the heap
pub struct StarlarkStrNRepr<const N: usize> {
    repr: AValueRepr<StarlarkStr>,
    payload: [u8; N],
}

impl<const N: usize> StarlarkStrNRepr<N> {
    /// Create a new [`StarlarkStrNRepr`] given a string of size `N`.
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

    /// Obtain the [`FrozenValue`] for a [`StarlarkStrNRepr`].
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

impl Borrow<str> for FrozenStringValue {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<'v> Borrow<str> for StringValue<'v> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Deref for FrozenStringValue {
    type Target = StarlarkStr;

    fn deref(&self) -> &StarlarkStr {
        &self.0.payload
    }
}

impl<'v> Deref for StringValue<'v> {
    type Target = StarlarkStr;

    fn deref(&self) -> &StarlarkStr {
        self.unpack_starlark_str()
    }
}

impl PartialEq for FrozenStringValue {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other) || self.as_str() == other.as_str()
    }
}

impl Eq for FrozenStringValue {}

impl Hash for FrozenStringValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl FrozenStringValue {
    /// Obtain the [`FrozenValue`] for a [`FrozenStringValue`].
    pub fn unpack(self) -> FrozenValue {
        FrozenValue::new_repr(self.0)
    }

    /// Construct without a check that the value contains a string.
    ///
    /// If passed value does not contain a string, it may lead to memory corruption.
    pub unsafe fn new_unchecked(value: FrozenValue) -> FrozenStringValue {
        debug_assert!(value.unpack_str().is_some());
        FrozenStringValue(&*(value.0.ptr_value() as *const AValueRepr<StarlarkStr>))
    }

    /// Construct from a value. Returns [`None`] if a value does not contain a string.
    pub fn new(value: FrozenValue) -> Option<FrozenStringValue> {
        if value.unpack_str().is_some() {
            Some(unsafe { Self::new_unchecked(value) })
        } else {
            None
        }
    }

    /// Get a string.
    pub fn as_str(self) -> &'static str {
        self.0.payload.unpack()
    }
}

impl<'v> PartialEq for StringValue<'v> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(other.0) || self.as_str() == other.as_str()
    }
}

impl<'v> Eq for StringValue<'v> {}

impl<'v> Hash for StringValue<'v> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl<'v> StringValue<'v> {
    /// Construct without a check that the value contains a string.
    ///
    /// If passed value does not contain a string, it may lead to memory corruption.
    pub unsafe fn new_unchecked(value: Value<'v>) -> StringValue<'v> {
        debug_assert!(value.unpack_str().is_some());
        StringValue(value)
    }

    /// Construct from a value. Returns [`None`] if a value does not contain a string.
    pub fn new(value: Value<'v>) -> Option<StringValue<'v>> {
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

    pub fn as_str(self) -> &'v str {
        self.unpack_starlark_str().unpack()
    }

    pub fn to_value(self) -> Value<'v> {
        self.0
    }

    /// Convert a value to a [`FrozenValue`] using a supplied [`Freezer`].
    pub fn freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenStringValue> {
        Ok(unsafe { FrozenStringValue::new_unchecked(freezer.freeze(self.0)?) })
    }
}

/// Common type for [`StringValue`] and [`FrozenStringValue`].
pub trait StringValueLike<'v>:
    Trace<'v> + CoerceKey<StringValue<'v>> + Debug + Copy + Clone + Dupe
{
    fn to_string_value(self) -> StringValue<'v>;
}

impl<'v> StringValueLike<'v> for StringValue<'v> {
    fn to_string_value(self) -> StringValue<'v> {
        self
    }
}

impl<'v> StringValueLike<'v> for FrozenStringValue {
    fn to_string_value(self) -> StringValue<'v> {
        StringValue(self.unpack().to_value())
    }
}

unsafe impl<'v> Trace<'v> for FrozenStringValue {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for StringValue<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.0.trace(tracer);
        debug_assert!(self.0.unpack_str().is_some());
    }
}

impl<'v> UnpackValue<'v> for StringValue<'v> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        StringValue::new(value)
    }
}

/// Create a [`FrozenStringValue`].
#[macro_export]
macro_rules! const_frozen_string {
    ($s:expr) => {{
        const N: usize = $s.len();
        static X: starlark::values::StarlarkStrNRepr<N> =
            starlark::values::StarlarkStrNRepr::new($s);
        X.erase()
    }};
}

pub(crate) static VALUE_EMPTY_STRING: StarlarkStrNRepr<0> = StarlarkStrNRepr::new("");

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

pub(crate) static VALUE_BYTE_STRINGS: [StarlarkStrNRepr<1>; 128] = [
    StarlarkStrNRepr::new("\x00"),
    StarlarkStrNRepr::new("\x01"),
    StarlarkStrNRepr::new("\x02"),
    StarlarkStrNRepr::new("\x03"),
    StarlarkStrNRepr::new("\x04"),
    StarlarkStrNRepr::new("\x05"),
    StarlarkStrNRepr::new("\x06"),
    StarlarkStrNRepr::new("\x07"),
    StarlarkStrNRepr::new("\x08"),
    StarlarkStrNRepr::new("\x09"),
    StarlarkStrNRepr::new("\x0A"),
    StarlarkStrNRepr::new("\x0B"),
    StarlarkStrNRepr::new("\x0C"),
    StarlarkStrNRepr::new("\x0D"),
    StarlarkStrNRepr::new("\x0E"),
    StarlarkStrNRepr::new("\x0F"),
    StarlarkStrNRepr::new("\x10"),
    StarlarkStrNRepr::new("\x11"),
    StarlarkStrNRepr::new("\x12"),
    StarlarkStrNRepr::new("\x13"),
    StarlarkStrNRepr::new("\x14"),
    StarlarkStrNRepr::new("\x15"),
    StarlarkStrNRepr::new("\x16"),
    StarlarkStrNRepr::new("\x17"),
    StarlarkStrNRepr::new("\x18"),
    StarlarkStrNRepr::new("\x19"),
    StarlarkStrNRepr::new("\x1A"),
    StarlarkStrNRepr::new("\x1B"),
    StarlarkStrNRepr::new("\x1C"),
    StarlarkStrNRepr::new("\x1D"),
    StarlarkStrNRepr::new("\x1E"),
    StarlarkStrNRepr::new("\x1F"),
    StarlarkStrNRepr::new("\x20"),
    StarlarkStrNRepr::new("\x21"),
    StarlarkStrNRepr::new("\x22"),
    StarlarkStrNRepr::new("\x23"),
    StarlarkStrNRepr::new("\x24"),
    StarlarkStrNRepr::new("\x25"),
    StarlarkStrNRepr::new("\x26"),
    StarlarkStrNRepr::new("\x27"),
    StarlarkStrNRepr::new("\x28"),
    StarlarkStrNRepr::new("\x29"),
    StarlarkStrNRepr::new("\x2A"),
    StarlarkStrNRepr::new("\x2B"),
    StarlarkStrNRepr::new("\x2C"),
    StarlarkStrNRepr::new("\x2D"),
    StarlarkStrNRepr::new("\x2E"),
    StarlarkStrNRepr::new("\x2F"),
    StarlarkStrNRepr::new("\x30"),
    StarlarkStrNRepr::new("\x31"),
    StarlarkStrNRepr::new("\x32"),
    StarlarkStrNRepr::new("\x33"),
    StarlarkStrNRepr::new("\x34"),
    StarlarkStrNRepr::new("\x35"),
    StarlarkStrNRepr::new("\x36"),
    StarlarkStrNRepr::new("\x37"),
    StarlarkStrNRepr::new("\x38"),
    StarlarkStrNRepr::new("\x39"),
    StarlarkStrNRepr::new("\x3A"),
    StarlarkStrNRepr::new("\x3B"),
    StarlarkStrNRepr::new("\x3C"),
    StarlarkStrNRepr::new("\x3D"),
    StarlarkStrNRepr::new("\x3E"),
    StarlarkStrNRepr::new("\x3F"),
    StarlarkStrNRepr::new("\x40"),
    StarlarkStrNRepr::new("\x41"),
    StarlarkStrNRepr::new("\x42"),
    StarlarkStrNRepr::new("\x43"),
    StarlarkStrNRepr::new("\x44"),
    StarlarkStrNRepr::new("\x45"),
    StarlarkStrNRepr::new("\x46"),
    StarlarkStrNRepr::new("\x47"),
    StarlarkStrNRepr::new("\x48"),
    StarlarkStrNRepr::new("\x49"),
    StarlarkStrNRepr::new("\x4A"),
    StarlarkStrNRepr::new("\x4B"),
    StarlarkStrNRepr::new("\x4C"),
    StarlarkStrNRepr::new("\x4D"),
    StarlarkStrNRepr::new("\x4E"),
    StarlarkStrNRepr::new("\x4F"),
    StarlarkStrNRepr::new("\x50"),
    StarlarkStrNRepr::new("\x51"),
    StarlarkStrNRepr::new("\x52"),
    StarlarkStrNRepr::new("\x53"),
    StarlarkStrNRepr::new("\x54"),
    StarlarkStrNRepr::new("\x55"),
    StarlarkStrNRepr::new("\x56"),
    StarlarkStrNRepr::new("\x57"),
    StarlarkStrNRepr::new("\x58"),
    StarlarkStrNRepr::new("\x59"),
    StarlarkStrNRepr::new("\x5A"),
    StarlarkStrNRepr::new("\x5B"),
    StarlarkStrNRepr::new("\x5C"),
    StarlarkStrNRepr::new("\x5D"),
    StarlarkStrNRepr::new("\x5E"),
    StarlarkStrNRepr::new("\x5F"),
    StarlarkStrNRepr::new("\x60"),
    StarlarkStrNRepr::new("\x61"),
    StarlarkStrNRepr::new("\x62"),
    StarlarkStrNRepr::new("\x63"),
    StarlarkStrNRepr::new("\x64"),
    StarlarkStrNRepr::new("\x65"),
    StarlarkStrNRepr::new("\x66"),
    StarlarkStrNRepr::new("\x67"),
    StarlarkStrNRepr::new("\x68"),
    StarlarkStrNRepr::new("\x69"),
    StarlarkStrNRepr::new("\x6A"),
    StarlarkStrNRepr::new("\x6B"),
    StarlarkStrNRepr::new("\x6C"),
    StarlarkStrNRepr::new("\x6D"),
    StarlarkStrNRepr::new("\x6E"),
    StarlarkStrNRepr::new("\x6F"),
    StarlarkStrNRepr::new("\x70"),
    StarlarkStrNRepr::new("\x71"),
    StarlarkStrNRepr::new("\x72"),
    StarlarkStrNRepr::new("\x73"),
    StarlarkStrNRepr::new("\x74"),
    StarlarkStrNRepr::new("\x75"),
    StarlarkStrNRepr::new("\x76"),
    StarlarkStrNRepr::new("\x77"),
    StarlarkStrNRepr::new("\x78"),
    StarlarkStrNRepr::new("\x79"),
    StarlarkStrNRepr::new("\x7A"),
    StarlarkStrNRepr::new("\x7B"),
    StarlarkStrNRepr::new("\x7C"),
    StarlarkStrNRepr::new("\x7D"),
    StarlarkStrNRepr::new("\x7E"),
    StarlarkStrNRepr::new("\x7F"),
];
