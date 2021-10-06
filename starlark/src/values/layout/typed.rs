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
    fmt,
    fmt::{Debug, Display, Formatter},
    marker,
};

use gazebo::dupe::Dupe;

use crate::{
    gazebo::any::AnyLifetime,
    values::{FrozenValue, PointerI32, StarlarkValue, Value, ValueLike},
};

/// [`FrozenValue`] wrapper which asserts contained value is of type `<T>`.
pub struct FrozenValueTyped<'v, T: StarlarkValue<'v>>(FrozenValue, marker::PhantomData<&'v T>);

impl<'v, T: StarlarkValue<'v>> Clone for FrozenValueTyped<'v, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'v, T: StarlarkValue<'v>> Copy for FrozenValueTyped<'v, T> {}
impl<'v, T: StarlarkValue<'v>> Dupe for FrozenValueTyped<'v, T> {}

impl<'v, T: StarlarkValue<'v>> Debug for FrozenValueTyped<'v, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FrozenValueType").field(&self.0).finish()
    }
}

impl<'v, T: StarlarkValue<'v>> Display for FrozenValueTyped<'v, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<'v, T: StarlarkValue<'v>> FrozenValueTyped<'v, T> {
    /// Downcast.
    pub fn new(value: FrozenValue) -> Option<FrozenValueTyped<'v, T>> {
        value.downcast_ref::<T>()?;
        Some(FrozenValueTyped(value, marker::PhantomData))
    }

    pub fn to_frozen_value(self) -> FrozenValue {
        self.0
    }

    pub fn to_value(self) -> Value<'v> {
        self.0.to_value()
    }

    pub fn as_ref(self) -> &'v T {
        // `FrozenValueTyped` is OK for `int`, but we cannot have a pointer to that int.
        assert!(T::static_type_id() != PointerI32::static_type_id());

        unsafe { &self.0.0.unpack_ptr_no_int_unchecked().as_repr().payload }
    }
}
