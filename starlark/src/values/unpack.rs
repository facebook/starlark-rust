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

//! Parameter conversion utilities for `starlark_module` macros.

use crate::values::{list::List, tuple::Tuple, ComplexValue, Value};
use gazebo::cell::ARef;
use std::{cell::RefMut, marker::PhantomData, ops::Deref};

/// How to convert a [`Value`] to a Rust type. Required for all arguments in a [`#[starlark_module]`](macro@starlark_module) definition.
pub trait UnpackValue<'v>: Sized {
    /// Given a [`Value`], try and unpack it into the given type, which may involve some element of conversion.
    /// The `heap` argument is _usually_ not required.
    fn unpack_value(value: Value<'v>) -> Option<Self>;
}

impl<'v> UnpackValue<'v> for Value<'v> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        Some(value)
    }
}

/// A wrapper that keeps the original value on the heap for use elsewhere,
/// and also, when unpacked, unpacks the value to validate it is of
/// the correct type. Has an [`UnpackValue`] instance, so often used as
/// an argument to [`#[starlark_module]`](macro@starlark_module) defined
/// functions.
///
/// Two container specializations of this are [`ListOf`](crate::values::list::ListOf)
/// and [`DictOf`](crate::values::dict::DictOf), which
/// validate the types of their containers on unpack, but do not store the
/// resulting Vec/Map
#[derive(Debug)]
pub struct ValueOf<'v, T: UnpackValue<'v>> {
    /// The original [`Value`] on the same heap.
    pub value: Value<'v>,
    /// The value that was unpacked.
    pub typed: T,
}

impl<'v, T: UnpackValue<'v>> Deref for ValueOf<'v, T> {
    type Target = Value<'v>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for ValueOf<'v, T> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        let typed = T::unpack_value(value)?;
        Some(Self { value, typed })
    }
}

/// Unpack a [`Value`] which is a reference to an underlying type.
///
/// Usually implemented by [`starlark_simple_value!`] or [`starlark_complex_value!`].
/// The from value instance for container types, e.g. [`List`](crate::values::list::List),
/// can work if the underlying value matches or is the frozen variant,
/// e.g. either [`List`](crate::values::list::List) or [`FrozenList`](crate::values::list::FrozenList).
pub trait FromValue<'v> {
    fn from_value(value: Value<'v>) -> Option<ARef<'v, Self>>;
}

impl<'v, T: FromValue<'v>> UnpackValue<'v> for ARef<'v, T> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        T::from_value(value)
    }
}

/// A wrapper around a mutable value that implements the [`UnpackValue`] trait,
/// allowing it to be used as an argument to [`#[starlark_module]`](macro@starlark_module)
/// defined functions.
///
/// The [`UnpackValue`] implementation validates that the type is correct, but not that
/// the value is mutable. The subsequet [`get_ref_mut`](ValueOfMut::get_ref_mut)
/// checks the value is actually mutable.
#[derive(Debug)]
pub struct ValueOfMut<'v, T: ComplexValue<'v>> {
    // We can't expose this directly, since the user might change it,
    // negating the check we did when constructing
    value: Value<'v>,
    phantom: PhantomData<T>,
}

impl<'v, T: ComplexValue<'v>> UnpackValue<'v> for ValueOfMut<'v, T> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        if value.get_aref().as_dyn_any().is::<T>() {
            Some(ValueOfMut {
                value,
                phantom: PhantomData,
            })
        } else {
            None
        }
    }
}

impl<'v, T: ComplexValue<'v>> ValueOfMut<'v, T> {
    /// Get the underlying [`Value`] on the original heap.
    pub fn value(&self) -> Value<'v> {
        self.value
    }

    pub fn get_aref(&self) -> ARef<'v, T> {
        // The `unwrap` won't fail because we checked at construction time.
        let vref = self.value.get_aref();
        ARef::map(vref, |any| any.as_dyn_any().downcast_ref::<T>().unwrap())
    }

    /// Get the value for mutation. Note that while the value is held for mutation,
    /// any other operation that accesses the value for non-mutable purposes
    /// might panic, so try and scope access as tightly as possible.
    pub fn get_ref_mut(&self) -> anyhow::Result<RefMut<'v, T>> {
        let vref = self.value.get_ref_mut()?;
        Ok(RefMut::map(vref, |any| {
            // The `unwrap` won't fail because we checked at construction time.
            any.as_dyn_any_mut().downcast_mut::<T>().unwrap()
        }))
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for Vec<T> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        if let Some(o) = List::from_value(value) {
            o.iter().map(T::unpack_value).collect::<Option<Vec<_>>>()
        } else if let Some(o) = Tuple::from_value(value) {
            o.iter().map(T::unpack_value).collect::<Option<Vec<_>>>()
        } else {
            None
        }
    }
}
