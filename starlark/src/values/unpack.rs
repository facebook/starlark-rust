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

/// Types implementing this type may appear in function parameter types
/// in `starlark_module` macro function signatures.
pub trait UnpackValue<'v>: Sized {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self>;
}

impl<'v> UnpackValue<'v> for Value<'v> {
    fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
        Some(value)
    }
}

/// A wrapper that keeps the original value on the heap for use elsewhere in the
/// interpreter, and also, when unpacked, unpacks the value to validate it is of
/// the correct type.
///
/// Two container specializations of this are `ListOf` and `DictOf`, which
/// validate the types of their containers on unpack, but do not store the
/// resulting Vec/Map
#[derive(Debug)]
pub struct ValueOf<'v, T: UnpackValue<'v>> {
    pub value: Value<'v>,
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

pub trait FromValue<'v>: Sized {
    fn from_value(value: Value<'v>) -> Option<ARef<'v, Self>>;
}

impl<'v, T: FromValue<'v>> UnpackValue<'v> for ARef<'v, T> {
    fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
        T::from_value(value)
    }
}
