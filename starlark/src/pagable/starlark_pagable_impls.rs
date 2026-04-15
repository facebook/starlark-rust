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

//! `StarlarkSerialize` and `StarlarkDeserialize` impls for common types
//! that delegate to their `PagableSerialize`/`PagableDeserialize` impls.
//!
//! This allows these types to be used directly in `#[derive(StarlarkPagable)]`
//! without needing `#[starlark_pagable(pagable)]`.

use pagable::PagableDeserialize;
use pagable::PagableSerialize;
use starlark_map::Hashed;
use starlark_map::small_map::SmallMap;

use crate::pagable::starlark_deserialize::StarlarkDeserialize;
use crate::pagable::starlark_deserialize::StarlarkDeserializeContext;
use crate::pagable::starlark_serialize::StarlarkSerialize;
use crate::pagable::starlark_serialize::StarlarkSerializeContext;
use crate::values::FrozenStringValue;
use crate::values::FrozenValue;
use crate::values::ValueLike;

/// Implement `StarlarkSerialize` and `StarlarkDeserialize` for a type
/// by delegating to its `PagableSerialize`/`PagableDeserialize` impls.
macro_rules! impl_starlark_via_pagable {
    ($($ty:ty),* $(,)?) => {
        $(
            impl StarlarkSerialize for $ty {
                fn starlark_serialize(&self, ctx: &mut dyn StarlarkSerializeContext) -> crate::Result<()> {
                    PagableSerialize::pagable_serialize(self, ctx.pagable())?;
                    Ok(())
                }
            }

            impl StarlarkDeserialize for $ty {
                fn starlark_deserialize(ctx: &mut dyn StarlarkDeserializeContext<'_>) -> crate::Result<Self> {
                    Ok(<$ty as PagableDeserialize>::pagable_deserialize(ctx.pagable())?)
                }
            }
        )*
    };
}

impl_starlark_via_pagable!(
    bool, u8, u16, u32, u64, usize, i8, i16, i32, i64, f32, f64, String,
);

impl<T: StarlarkSerialize> StarlarkSerialize for Vec<T> {
    fn starlark_serialize(&self, ctx: &mut dyn StarlarkSerializeContext) -> crate::Result<()> {
        self.len().pagable_serialize(ctx.pagable())?;
        for elem in self {
            elem.starlark_serialize(ctx)?;
        }
        Ok(())
    }
}

impl<T: StarlarkDeserialize> StarlarkDeserialize for Vec<T> {
    fn starlark_deserialize(ctx: &mut dyn StarlarkDeserializeContext<'_>) -> crate::Result<Self> {
        let len = usize::pagable_deserialize(ctx.pagable())?;
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(T::starlark_deserialize(ctx)?);
        }
        Ok(v)
    }
}

impl<T: StarlarkSerialize> StarlarkSerialize for Box<T> {
    fn starlark_serialize(&self, ctx: &mut dyn StarlarkSerializeContext) -> crate::Result<()> {
        (**self).starlark_serialize(ctx)
    }
}

impl<T: StarlarkDeserialize> StarlarkDeserialize for Box<T> {
    fn starlark_deserialize(ctx: &mut dyn StarlarkDeserializeContext<'_>) -> crate::Result<Self> {
        Ok(Box::new(T::starlark_deserialize(ctx)?))
    }
}

impl<T: StarlarkSerialize> StarlarkSerialize for Option<T> {
    fn starlark_serialize(&self, ctx: &mut dyn StarlarkSerializeContext) -> crate::Result<()> {
        match self {
            Some(v) => {
                true.pagable_serialize(ctx.pagable())?;
                v.starlark_serialize(ctx)?;
            }
            None => {
                false.pagable_serialize(ctx.pagable())?;
            }
        }
        Ok(())
    }
}

impl<T: StarlarkDeserialize> StarlarkDeserialize for Option<T> {
    fn starlark_deserialize(ctx: &mut dyn StarlarkDeserializeContext<'_>) -> crate::Result<Self> {
        let is_some = bool::pagable_deserialize(ctx.pagable())?;
        if is_some {
            Ok(Some(T::starlark_deserialize(ctx)?))
        } else {
            Ok(None)
        }
    }
}

// ============================================================================
// SmallMap
// ============================================================================

impl<K: StarlarkSerialize, V: StarlarkSerialize> StarlarkSerialize for SmallMap<K, V> {
    fn starlark_serialize(&self, ctx: &mut dyn StarlarkSerializeContext) -> crate::Result<()> {
        self.len().pagable_serialize(ctx.pagable())?;
        for (k, v) in self.iter() {
            k.starlark_serialize(ctx)?;
            v.starlark_serialize(ctx)?;
        }
        Ok(())
    }
}

impl<K: SmallMapKeyDeserialize, V: StarlarkDeserialize> StarlarkDeserialize for SmallMap<K, V> {
    fn starlark_deserialize(ctx: &mut dyn StarlarkDeserializeContext<'_>) -> crate::Result<Self> {
        let len = usize::pagable_deserialize(ctx.pagable())?;
        let mut map = SmallMap::with_capacity(len);
        for _ in 0..len {
            let hashed_k = K::starlark_deserialize_hashed(ctx)?;
            let v = V::starlark_deserialize(ctx)?;
            map.insert_hashed(hashed_k, v);
        }
        Ok(map)
    }
}

/// Trait for types that can be deserialized as SmallMap keys.
/// Bridges the gap between types with `Hash` (use `Hashed::new`) and
/// starlark value types (use `get_hashed()`).
pub(crate) trait SmallMapKeyDeserialize: StarlarkDeserialize + Eq + Sized {
    fn starlark_deserialize_hashed(
        ctx: &mut dyn StarlarkDeserializeContext<'_>,
    ) -> crate::Result<Hashed<Self>>;
}

/// Impl for types with `Hash` — hash is computed via the standard `Hash` trait.
macro_rules! impl_small_map_key_hash {
    ($($ty:ty),* $(,)?) => {
        $(
            impl SmallMapKeyDeserialize for $ty {
                fn starlark_deserialize_hashed(
                    ctx: &mut dyn StarlarkDeserializeContext<'_>,
                ) -> crate::Result<Hashed<Self>> {
                    let k = Self::starlark_deserialize(ctx)?;
                    Ok(Hashed::new(k))
                }
            }
        )*
    };
}

impl_small_map_key_hash!(String, bool, u8, u16, u32, u64, usize, i8, i16, i32, i64);

/// FrozenValue: no `Hash` trait, use `get_hashed()` from `ValueLike`.
/// The value is already ensure_initialized by `deserialize_frozen_value`.
impl SmallMapKeyDeserialize for FrozenValue {
    fn starlark_deserialize_hashed(
        ctx: &mut dyn StarlarkDeserializeContext<'_>,
    ) -> crate::Result<Hashed<Self>> {
        let fv = FrozenValue::starlark_deserialize(ctx)?;
        fv.get_hashed()
    }
}

/// FrozenStringValue: string hash is infallible.
impl SmallMapKeyDeserialize for FrozenStringValue {
    fn starlark_deserialize_hashed(
        ctx: &mut dyn StarlarkDeserializeContext<'_>,
    ) -> crate::Result<Hashed<Self>> {
        let fsv = FrozenStringValue::starlark_deserialize(ctx)?;
        Ok(fsv.get_hashed())
    }
}
