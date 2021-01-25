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

//! Define the any type for Starlark.

use crate::values::{
    AllocFrozenValue, AllocValue, FrozenHeap, FrozenValue, Heap, ImmutableValue, TypedValue, Value,
};
use gazebo::{any::AnyLifetime, cell::ARef};
use std::{
    any::Any,
    fmt::{self, Debug},
};

trait AnyDebugSendSync: Any + Debug + Send + Sync {
    fn as_any(&self) -> &dyn Any;
}
impl<T: Any + Debug + Send + Sync> AnyDebugSendSync for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// A type that can be passed around as a Starlark `Value`, but in most
/// ways is uninteresting/opaque to Starlark. Constructed with `new` and
/// decomposed with `get`.
#[derive(AnyLifetime)]
pub struct StarlarkAny(Box<dyn AnyDebugSendSync>);

impl StarlarkAny {
    pub const TYPE: &'static str = "any";
}

impl Debug for StarlarkAny {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl StarlarkAny {
    /// Create a new `StarlarkAny` value. Such a value can be allocated on a heap with
    /// `heap.alloc(StarlarkAny::new(x))`.
    pub fn new<T: Any + Debug + Send + Sync>(x: T) -> Self {
        Self(box x)
    }

    /// Extract a `Value` that contains a `StarlarkAny` underneath. Returns `None` if
    /// the value does not match the expected type.
    pub fn get<'v, T: Any + Debug + Send + Sync>(x: Value<'v>) -> Option<ARef<'v, T>> {
        let x: ARef<'v, Self> = x.downcast_ref()?;
        let x: ARef<'v, dyn Any> = ARef::map(x, |x| x.0.as_ref().as_any());
        if x.is::<T>() {
            // We checked it works first, so the downcast_ref can't fail
            Some(ARef::map(x, |x| x.downcast_ref::<T>().unwrap()))
        } else {
            None
        }
    }
}

impl<'v> AllocFrozenValue<'v> for StarlarkAny {
    fn alloc_frozen_value(self, heap: &'v FrozenHeap) -> FrozenValue {
        heap.alloc_immutable(self)
    }
}

impl<'v> AllocValue<'v> for StarlarkAny {
    fn alloc_value(self, heap: &'v Heap) -> Value {
        heap.alloc_immutable(self)
    }
}

impl ImmutableValue<'_> for StarlarkAny {}

/// Define the any type
impl TypedValue<'_> for StarlarkAny {
    starlark_type!(StarlarkAny::TYPE);
}
