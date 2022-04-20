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
    fmt::{Debug, Display},
};

use gazebo::{
    coerce::{Coerce, CoerceKey},
    prelude::*,
};
use indexmap::Equivalent;

use crate::{
    collections::{BorrowHashed, Hashed},
    values::{string::StarlarkStr, Freeze, Freezer, FrozenValueTyped, Trace, Value, ValueTyped},
};

/// Convenient type alias.
///
/// We use `FrozenValueTyped<StarlarkStr>` often, but also we define more operations
/// on `FrozenValueTyped<StarlarkStr>` than on generic `FrozenValueTyped<T>`.
///
/// Note there's a macro `const_frozen_string!` to statically allocate `FrozenStringValue`:
///
/// ```
/// use starlark::const_frozen_string;
/// use starlark::values::{FrozenStringValue, FrozenValue};
///
/// let fv: FrozenStringValue = const_frozen_string!("magic");
/// assert_eq!("magic", fv.as_str());
/// ```
pub type FrozenStringValue = FrozenValueTyped<'static, StarlarkStr>;

/// Convenient type alias.
///
/// We use `ValueTyped<StarlarkStr>` often, but also we define more operations
/// on `ValueTyped<StarlarkStr>` than on generic `ValueTyped<T>`.
pub type StringValue<'v> = ValueTyped<'v, StarlarkStr>;

// TODO(nga): move everything below to `ValueTyped`.

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
    /// Get self along with the hash.
    pub fn get_hashed(self) -> Hashed<Self> {
        Hashed::new_unchecked(self.get_hash(), self)
    }

    /// Get the string reference along with the hash.
    pub fn get_hashed_str(self) -> BorrowHashed<'static, str> {
        BorrowHashed::new_unchecked(self.get_hash(), self.as_str())
    }
}

impl<'v> StringValue<'v> {
    /// Convert a value to a [`FrozenStringValue`] using a supplied [`Freezer`].
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
        self.to_value_typed()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        collections::{BorrowHashed, Hashed},
        values::{FrozenHeap, FrozenStringValue, FrozenValue, Heap, StringValue, Value, ValueLike},
    };

    #[test]
    fn test_string_hashes() {
        let expected = BorrowHashed::new("xyz").hash();

        let heap = Heap::new();
        let s: StringValue = heap.alloc_str("xyz");
        assert_eq!(expected, Hashed::new(s).hash());
        let v: Value = heap.alloc_str("xyz").to_value();
        assert_eq!(expected, v.get_hashed().unwrap().hash());

        let heap = FrozenHeap::new();
        let fs: FrozenStringValue = heap.alloc_str("xyz");
        assert_eq!(expected, Hashed::new(fs).hash());
        let fv: FrozenValue = heap.alloc_str("xyz").to_frozen_value();
        assert_eq!(expected, fv.get_hashed().unwrap().hash());
    }
}
