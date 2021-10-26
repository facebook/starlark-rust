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

use std::{marker, marker::PhantomData};

use gazebo::prelude::*;
use thiserror::Error;

use crate::{
    collections::{Hashed, SmallMap},
    values::{Freezer, FrozenStringValue, FrozenValue, StringValue, Value},
};

/// Need to be implemented for non-simple `StarlarkValue`.
///
/// This is called on freeze of the heap. Must produce a replacement object to place
/// in the frozen heap.
///
/// For relatively simple cases it can be implemented with `#[derive(Freeze)]`:
///
/// ```
/// # struct AdditionalData;
///
/// use starlark::values::Freeze;
///
/// #[derive(Freeze)]
/// struct MyType<V> {
///     value: V,
///     // This field does not implement `Freeze`, but we can use it as is for freeze.
///     #[freeze(identity)]
///     data: AdditionalData,
/// }
/// ```
pub trait Freeze {
    type Frozen;

    /// Freeze a value. The frozen value _must_ be equal to the original,
    /// and produce the same hash.
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen>;
}

impl Freeze for String {
    type Frozen = String;

    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<String> {
        Ok(self)
    }
}

impl Freeze for i32 {
    type Frozen = i32;

    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<i32> {
        Ok(self)
    }
}

impl Freeze for usize {
    type Frozen = usize;

    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<usize> {
        Ok(self)
    }
}

impl Freeze for bool {
    type Frozen = bool;

    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<bool> {
        Ok(self)
    }
}

impl<'v, T: 'static> Freeze for marker::PhantomData<&'v T> {
    type Frozen = PhantomData<&'static T>;

    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<PhantomData<&'static T>> {
        Ok(marker::PhantomData)
    }
}

impl<T> Freeze for Vec<T>
where
    T: Freeze,
{
    type Frozen = Vec<T::Frozen>;

    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Vec<T::Frozen>> {
        self.into_try_map(|v| v.freeze(freezer))
    }
}

impl<T> Freeze for Option<T>
where
    T: Freeze,
{
    type Frozen = Option<T::Frozen>;

    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Option<T::Frozen>> {
        self.into_try_map(|v| v.freeze(freezer))
    }
}

#[derive(Debug, Error)]
enum FreezeFieldError {
    #[error("Non-unique map key")]
    NonUniqueMapKey,
}

impl<K, V> Freeze for SmallMap<K, V>
where
    K: Freeze,
    V: Freeze,
    K: Eq,
    K::Frozen: Eq,
{
    type Frozen = SmallMap<K::Frozen, V::Frozen>;

    fn freeze(self, freezer: &Freezer) -> anyhow::Result<SmallMap<K::Frozen, V::Frozen>> {
        let mut result = SmallMap::with_capacity(self.len());
        for (k, v) in self.into_iter_hashed() {
            let hash = k.hash();
            let k = k.into_key().freeze(freezer)?;
            // Trust hash is unchanged.
            let k = Hashed::new_unchecked(hash, k);
            let v = v.freeze(freezer)?;
            let prev = result.insert_hashed(k, v);
            if prev.is_some() {
                return Err(FreezeFieldError::NonUniqueMapKey.into());
            }
        }
        Ok(result)
    }
}

impl<'v> Freeze for Value<'v> {
    type Frozen = FrozenValue;

    fn freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenValue> {
        freezer.freeze(self)
    }
}

impl<'v> Freeze for StringValue<'v> {
    type Frozen = FrozenStringValue;

    fn freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenStringValue> {
        self.freeze(freezer)
    }
}

impl Freeze for FrozenStringValue {
    type Frozen = FrozenStringValue;

    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<FrozenStringValue> {
        Ok(self)
    }
}
