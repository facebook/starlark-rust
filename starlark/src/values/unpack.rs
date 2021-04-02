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

use crate::values::{Heap, Value};
use gazebo::cell::ARef;
use std::ops::Deref;

/// How to convert a [`Value`] to a Rust type. Required for all arguments in a [`#[starlark_module]`](macro@starlark_module) definition.
pub trait UnpackValue<'v>: Sized {
    /// Given a [`Value`], try and unpack it into the given type, which may involve some element of conversion.
    /// The `heap` argument is _usually_ not required.
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self>;
}

impl<'v> UnpackValue<'v> for Value<'v> {
    fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
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
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let typed = T::unpack_value(value, heap)?;
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
    fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
        T::from_value(value)
    }
}
