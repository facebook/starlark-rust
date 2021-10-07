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

use gazebo::prelude::*;

use crate::{
    gazebo::any::AnyLifetime,
    values::{FrozenValue, PointerI32, StarlarkValue, Value, ValueLike},
};

/// [`FrozenValue`] wrapper which asserts contained value is of type `<T>`.
#[derive(Copy_, Clone_, Dupe_)]
pub struct FrozenValueTyped<'v, T: StarlarkValue<'v>>(FrozenValue, marker::PhantomData<&'v T>);

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
        if T::static_type_id() == PointerI32::static_type_id() {
            unsafe {
                transmute!(
                    &PointerI32,
                    &T,
                    PointerI32::new(self.0.0.unpack_int_unchecked())
                )
            }
        } else {
            unsafe { &self.0.0.unpack_ptr_no_int_unchecked().as_repr().payload }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::values::{FrozenValue, FrozenValueTyped, PointerI32, StarlarkValue};

    #[test]
    fn int() {
        let v = FrozenValueTyped::<PointerI32>::new(FrozenValue::new_int(17)).unwrap();
        assert_eq!(17, v.as_ref().to_int().unwrap());
    }
}
