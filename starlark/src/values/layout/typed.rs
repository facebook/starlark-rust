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
    ops::Deref,
};

use gazebo::{cast, prelude::*};

use crate::{
    gazebo::any::AnyLifetime,
    values::{
        layout::{arena::AValueRepr, avalue::AValue},
        AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, PointerI32, StarlarkValue,
        Trace, Tracer, UnpackValue, Value, ValueLike,
    },
};

/// [`Value`] wrapper which asserts contained value is of type `<T>`.
#[derive(Copy_, Clone_, Dupe_)]
pub struct ValueTyped<'v, T: StarlarkValue<'v>>(Value<'v>, marker::PhantomData<&'v T>);
/// [`FrozenValue`] wrapper which asserts contained value is of type `<T>`.
#[derive(Copy_, Clone_, Dupe_)]
pub struct FrozenValueTyped<'v, T: StarlarkValue<'v>>(FrozenValue, marker::PhantomData<&'v T>);

impl<'v, T: StarlarkValue<'v>> Debug for ValueTyped<'v, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ValueType").field(&self.0).finish()
    }
}

impl<'v, T: StarlarkValue<'v>> Debug for FrozenValueTyped<'v, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FrozenValueType").field(&self.0).finish()
    }
}

impl<'v, T: StarlarkValue<'v>> Display for ValueTyped<'v, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<'v, T: StarlarkValue<'v>> Display for FrozenValueTyped<'v, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<'v, T: StarlarkValue<'v>> ValueTyped<'v, T> {
    /// Downcast.
    pub fn new(value: Value<'v>) -> Option<ValueTyped<'v, T>> {
        value.downcast_ref::<T>()?;
        Some(ValueTyped(value, marker::PhantomData))
    }

    pub unsafe fn new_unchecked(value: Value<'v>) -> ValueTyped<'v, T> {
        debug_assert!(value.downcast_ref::<T>().is_some());
        ValueTyped(value, marker::PhantomData)
    }

    pub(crate) fn new_repr<A: AValue<'v, StarlarkValue = T>>(
        repr: &'v AValueRepr<A>,
    ) -> ValueTyped<'v, T> {
        ValueTyped(Value::new_repr(repr), marker::PhantomData)
    }

    pub fn to_value(self) -> Value<'v> {
        self.0
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

impl<'v, T: StarlarkValue<'v>> FrozenValueTyped<'v, T> {
    /// Downcast.
    pub fn new(value: FrozenValue) -> Option<FrozenValueTyped<'v, T>> {
        value.downcast_ref::<T>()?;
        Some(FrozenValueTyped(value, marker::PhantomData))
    }

    pub(crate) fn new_repr<A: AValue<'v, StarlarkValue = T>>(
        repr: &'v AValueRepr<A>,
    ) -> FrozenValueTyped<'v, T> {
        // drop lifetime: `FrozenValue` is not (yet) parameterized with lifetime.
        let header = unsafe { cast::ptr_lifetime(&repr.header) };
        FrozenValueTyped(
            FrozenValue::new_ptr(header, A::is_str()),
            marker::PhantomData,
        )
    }

    pub fn to_frozen_value(self) -> FrozenValue {
        self.0
    }

    pub fn to_value(self) -> Value<'v> {
        self.0.to_value()
    }

    pub fn to_value_typed(self) -> ValueTyped<'v, T> {
        unsafe { ValueTyped::new_unchecked(self.0.to_value()) }
    }

    pub fn as_ref(self) -> &'v T {
        self.to_value_typed().as_ref()
    }
}

unsafe impl<'v, T: StarlarkValue<'v>> Trace<'v> for ValueTyped<'v, T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        tracer.trace(&mut self.0);
        // If type of value changed, dereference will produce the wrong object type.
        debug_assert!(self.0.downcast_ref::<T>().is_some());
    }
}

impl<'v, T: StarlarkValue<'v>> Deref for FrozenValueTyped<'v, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<'v, T: StarlarkValue<'v>> Deref for ValueTyped<'v, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<'v, T: StarlarkValue<'v>> UnpackValue<'v> for ValueTyped<'v, T> {
    fn expected() -> String {
        T::get_type_value_static().as_str().to_owned()
    }

    fn unpack_value(value: Value<'v>) -> Option<Self> {
        ValueTyped::new(value)
    }
}

impl<'v, T: StarlarkValue<'v>> AllocValue<'v> for ValueTyped<'v, T> {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        self.0
    }
}

impl<'v, T: StarlarkValue<'v>> AllocValue<'v> for FrozenValueTyped<'v, T> {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        self.0.to_value()
    }
}

impl<'v, T: StarlarkValue<'v>> AllocFrozenValue for FrozenValueTyped<'v, T> {
    fn alloc_frozen_value(self, _heap: &FrozenHeap) -> FrozenValue {
        self.0
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
