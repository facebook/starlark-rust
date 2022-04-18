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
    cmp::Ordering,
    fmt,
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
    ops::Deref,
    ptr,
};

use gazebo::{
    any::AnyLifetime,
    coerce::{Coerce, CoerceKey},
    prelude::*,
};
use indexmap::Equivalent;

use crate::{
    collections::{BorrowHashed, Hashed},
    values::{
        layout::value::FrozenValue, string::StarlarkStr, AllocValue, Freeze, Freezer,
        FrozenValueTyped, Heap, Trace, Tracer, UnpackValue, Value, ValueTyped,
    },
};

/// Define a `&'static` [`str`] that can be converted to a [`FrozenValue`].
///
/// Usually used as:
///
/// ```
/// use starlark::const_frozen_string;
/// use starlark::values::{FrozenStringValue, FrozenValue};
///
/// let fv: FrozenValue =  const_frozen_string!("magic").unpack();
/// assert_eq!(Some("magic"), fv.to_value().unpack_str());
/// ```
#[derive(Copy, Clone, Dupe, Debug, AnyLifetime)]
#[repr(C)]
pub struct FrozenStringValue(FrozenValueTyped<'static, StarlarkStr>);

/// Wrapper for a [`Value`] which can only contain a [`StarlarkStr`].
#[derive(Copy, Clone, Dupe, Debug, AnyLifetime)]
#[repr(C)]
pub struct StringValue<'v>(ValueTyped<'v, StarlarkStr>);

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
    type Target = FrozenValueTyped<'static, StarlarkStr>;

    fn deref(&self) -> &FrozenValueTyped<'static, StarlarkStr> {
        &self.0
    }
}

impl<'v> Deref for StringValue<'v> {
    type Target = ValueTyped<'v, StarlarkStr>;

    fn deref(&self) -> &ValueTyped<'v, StarlarkStr> {
        &self.0
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

impl<'v> Equivalent<FrozenStringValue> for StringValue<'v> {
    fn equivalent(&self, key: &FrozenStringValue) -> bool {
        *self == key.to_string_value()
    }
}

impl<'v> Equivalent<StringValue<'v>> for FrozenStringValue {
    fn equivalent(&self, key: &StringValue<'v>) -> bool {
        self.to_string_value() == *key
    }
}

impl FrozenStringValue {
    /// Obtain the [`FrozenValue`] for a [`FrozenStringValue`].
    pub fn unpack(self) -> FrozenValue {
        self.0.to_frozen_value()
    }

    /// Construct without a check that the value contains a string.
    ///
    /// If passed value does not contain a string, it may lead to memory corruption.
    pub unsafe fn new_unchecked(value: FrozenValue) -> FrozenStringValue {
        FrozenStringValue(FrozenValueTyped::new_unchecked(value))
    }

    /// Construct from a value. Returns [`None`] if a value does not contain a string.
    pub fn new(value: FrozenValue) -> Option<FrozenStringValue> {
        FrozenValueTyped::new(value).map(FrozenStringValue)
    }

    pub(crate) fn as_starlark_str(self) -> &'static StarlarkStr {
        self.0.as_ref()
    }

    /// Get a string.
    pub fn as_str(self) -> &'static str {
        self.as_starlark_str().as_str()
    }

    /// Get self along with the hash.
    pub fn get_hashed(self) -> Hashed<Self> {
        Hashed::new_unchecked(self.get_hash(), self)
    }

    /// Get the string reference along with the hash.
    pub fn get_hashed_str(self) -> BorrowHashed<'static, str> {
        BorrowHashed::new_unchecked(self.get_hash(), self.as_str())
    }
}

impl<'v> PartialEq for StringValue<'v> {
    fn eq(&self, other: &Self) -> bool {
        self.to_value().ptr_eq(other.to_value()) || self.as_str() == other.as_str()
    }
}

impl<'v> Eq for StringValue<'v> {}

impl<'v> PartialEq<FrozenStringValue> for StringValue<'v> {
    fn eq(&self, other: &FrozenStringValue) -> bool {
        *self == other.to_string_value()
    }
}

impl<'v> PartialEq<StringValue<'v>> for FrozenStringValue {
    fn eq(&self, other: &StringValue<'v>) -> bool {
        self.to_string_value() == *other
    }
}

impl<'v> Hash for StringValue<'v> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl<'v> PartialOrd for StringValue<'v> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl<'v> Ord for StringValue<'v> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<'v> StringValue<'v> {
    /// Construct without a check that the value contains a string.
    ///
    /// If passed value does not contain a string, it may lead to memory corruption.
    pub unsafe fn new_unchecked(value: Value<'v>) -> StringValue<'v> {
        StringValue(ValueTyped::new_unchecked(value))
    }

    /// Construct from a value. Returns [`None`] if a value does not contain a string.
    pub fn new(value: Value<'v>) -> Option<StringValue<'v>> {
        ValueTyped::new(value).map(StringValue)
    }

    pub(crate) fn unpack_starlark_str(self) -> &'v StarlarkStr {
        debug_assert!(self.to_value().is_str());
        self.0.as_ref()
    }

    /// Get the Rust string reference.
    pub fn as_str(self) -> &'v str {
        self.unpack_starlark_str().as_str()
    }

    /// Convert to Starlark value.
    pub fn to_value(self) -> Value<'v> {
        self.0.to_value()
    }

    /// Convert a value to a [`FrozenValue`] using a supplied [`Freezer`].
    pub fn freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenStringValue> {
        Ok(unsafe { FrozenStringValue::new_unchecked(freezer.freeze(self.to_value())?) })
    }

    /// Get self along with the hash.
    pub fn get_hashed(self) -> Hashed<Self> {
        Hashed::new_unchecked(self.get_hash(), self)
    }

    /// Get the string reference along with the hash.
    pub fn get_hashed_str(self) -> BorrowHashed<'v, str> {
        BorrowHashed::new_unchecked(self.get_hash(), self.as_str())
    }

    /// If this string value is frozen, return it.
    pub fn unpack_frozen(self) -> Option<FrozenStringValue> {
        self.to_value()
            .unpack_frozen()
            .map(|s| unsafe { FrozenStringValue::new_unchecked(s) })
    }
}

impl<'v> Display for StringValue<'v> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Display for FrozenStringValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.to_string_value(), f)
    }
}

/// Common type for [`StringValue`] and [`FrozenStringValue`].
pub trait StringValueLike<'v>:
    Trace<'v>
    + Freeze<Frozen = FrozenStringValue>
    + CoerceKey<StringValue<'v>>
    + Display
    + Debug
    + Copy
    + Clone
    + Dupe
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
        unsafe { StringValue::new_unchecked(self.unpack().to_value()) }
    }
}

unsafe impl<'v> Trace<'v> for FrozenStringValue {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for StringValue<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.0.trace(tracer);
        debug_assert!(self.to_value().unpack_str().is_some());
    }
}

impl<'v> UnpackValue<'v> for StringValue<'v> {
    fn expected() -> String {
        "str".to_owned()
    }

    fn unpack_value(value: Value<'v>) -> Option<Self> {
        StringValue::new(value)
    }
}

impl<'v> AllocValue<'v> for StringValue<'v> {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        self.to_value()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        collections::Hashed,
        values::{FrozenHeap, FrozenStringValue, FrozenValue, Heap, StringValue, Value, ValueLike},
    };

    #[test]
    fn test_string_hashes() {
        let heap = Heap::new();
        let s: StringValue = heap.alloc_str("xyz");
        let v: Value = heap.alloc_str("xyz").to_value();
        assert_eq!(Hashed::new(s).hash(), v.get_hashed().unwrap().hash());

        let heap = FrozenHeap::new();
        let fs: FrozenStringValue = heap.alloc_str("xyz");
        let fv: FrozenValue = heap.alloc_str("xyz").unpack();
        assert_eq!(Hashed::new(fs).hash(), fv.get_hashed().unwrap().hash());

        assert_eq!(Hashed::new(s).hash(), Hashed::new(fs).hash());
    }
}
