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

//! A type [`StarlarkAny`] which can cheaply wrap any Rust value into a [`Value`].
//!
//! This is intended to be a low cost way to quickly wrap Rust types without much boilerplate.
//! For more advanced uses you should define an instance of [`StarlarkValue`].
//!
//! To use this type, usually you will return a [`StarlarkAny`] from a module function,
//! and consume it in another. As an example, we can cheaply wrap the
//! [`Duration`](std::time::Duration) type.
//!
//! ```
//! #[macro_use]
//! extern crate starlark;
//! # fn main() {
//! use starlark::assert::Assert;
//! use starlark::environment::GlobalsBuilder;
//! use starlark::values::Value;
//! use starlark::values::any::StarlarkAny;
//! use std::time::Instant;
//!
//! #[starlark_module]
//! fn globals(builder: &mut GlobalsBuilder) {
//!     fn start() -> StarlarkAny {
//!         Ok(StarlarkAny::new(Instant::now()))
//!     }
//!
//!     fn elapsed(x: Value) -> String {
//!         Ok(StarlarkAny::get::<Instant>(x).unwrap().elapsed().as_secs_f64().to_string())
//!     }
//! }
//!
//! let mut a = Assert::new();
//! a.globals_add(globals);
//! a.pass(r#"
//! duration = start()
//! y = 100
//! for x in range(100):
//!     y += x
//! print(elapsed(duration))
//! "#);
//! # }
//! ```

use crate::{
    starlark_simple_value,
    values::{StarlarkValue, Value, ValueLike},
};
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

/// A type that can be passed around as a Starlark [`Value`], but in most
/// ways is uninteresting/opaque to Starlark. Constructed with
/// [`new`](StarlarkAny::new) and decomposed with [`get`](StarlarkAny::get).
pub struct StarlarkAny(Box<dyn AnyDebugSendSync>);

impl StarlarkAny {
    /// The result of calling `type()` on [`StarlarkAny`].
    pub const TYPE: &'static str = "any";
}

starlark_simple_value!(StarlarkAny);

impl Debug for StarlarkAny {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl StarlarkAny {
    /// Create a new [`StarlarkAny`] value. Such a value can be allocated on a heap with
    /// `heap.alloc(StarlarkAny::new(x))`.
    pub fn new<T: Any + Debug + Send + Sync>(x: T) -> Self {
        Self(box x)
    }

    /// Extract from a [`Value`] that contains a [`StarlarkAny`] underneath. Returns [`None`] if
    /// the value does not match the expected type.
    pub fn get<'v, T: Any + Debug + Send + Sync>(x: Value<'v>) -> Option<&'v T> {
        let x: &'v Self = x.downcast_ref()?;
        let x: &'v dyn Any = x.0.as_ref().as_any();
        x.downcast_ref::<T>()
    }
}

/// Define the any type
impl StarlarkValue<'_> for StarlarkAny {
    starlark_type!(StarlarkAny::TYPE);
}
