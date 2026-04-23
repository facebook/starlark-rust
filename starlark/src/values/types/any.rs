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
//! use std::fmt;
//! use std::time::Instant;
//!
//! use starlark::assert::Assert;
//! use starlark::environment::GlobalsBuilder;
//! use starlark::values::Value;
//! use starlark::values::any::StarlarkAny;
//!
//! #[derive(Debug)]
//! struct MyInstant(Instant);
//!
//! starlark::register_starlark_any!(MyInstant);
//!
//! #[starlark_module]
//! fn globals(builder: &mut GlobalsBuilder) {
//!     fn start() -> anyhow::Result<StarlarkAny<MyInstant>> {
//!         Ok(StarlarkAny::new(MyInstant(Instant::now())))
//!     }
//!
//!     fn elapsed(x: Value) -> anyhow::Result<String> {
//!         Ok(StarlarkAny::<MyInstant>::get(x)
//!             .unwrap()
//!             .0
//!             .elapsed()
//!             .as_secs_f64()
//!             .to_string())
//!     }
//! }
//!
//! let mut a = Assert::new();
//! a.globals_add(globals);
//! a.pass(
//!     r#"
//! instant = start()
//! print(elapsed(instant))
//! "#,
//! );
//! # }
//! ```

use std::fmt;
use std::fmt::Debug;
use std::fmt::Display;
use std::ops::Deref;

use allocative::Allocative;
use dupe::Clone_;
use dupe::Copy_;
use dupe::Dupe_;
use starlark_derive::NoSerialize;
use starlark_derive::starlark_value;

use crate as starlark;
use crate::any::ProvidesStaticType;
use crate::pagable::vtable_register::VtableRegistered;
use crate::values::AllocValue;
use crate::values::Freeze;
use crate::values::FreezeResult;
use crate::values::Freezer;
use crate::values::FrozenHeap;
use crate::values::FrozenRef;
use crate::values::FrozenValue;
use crate::values::FrozenValueTyped;
use crate::values::Heap;
use crate::values::StarlarkValue;
use crate::values::Trace;
use crate::values::Tracer;
use crate::values::Value;
use crate::values::ValueLike;

/// A type that can be passed around as a Starlark [`Value`], but in most
/// ways is uninteresting/opaque to Starlark. Constructed with
/// [`new`](StarlarkAny::new) and decomposed with [`get`](StarlarkAny::get).
///
/// This is version for "simple" values (not requiring trace during GC).
/// For "complex" version check
/// [`StarlarkAnyComplex`](crate::values::types::any_complex::StarlarkAnyComplex).
#[derive(ProvidesStaticType, NoSerialize, Allocative, derive_more::Display)]
#[allocative(bound = "")]
#[display("{:?}", self)]
#[repr(transparent)]
pub struct StarlarkAny<T: Debug + Send + Sync + 'static>(
    #[allocative(skip)] // TODO(nga): do not skip.
    pub  T,
);

#[starlark_value(type = "any")]
impl<'v, T: Debug + Send + Sync + 'static> StarlarkValue<'v> for StarlarkAny<T> {
    type Canonical = Self;
}

impl<'v, T: StarlarkAnyBound> AllocValue<'v> for StarlarkAny<T> {
    fn alloc_value(self, heap: Heap<'v>) -> Value<'v> {
        heap.alloc_simple(self)
    }
}

impl<T: Debug + Send + Sync + 'static> Debug for StarlarkAny<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<T: Debug + Send + Sync + 'static> Deref for StarlarkAny<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T: Debug + Send + Sync + 'static> StarlarkAny<T> {
    /// Create a new [`StarlarkAny`] value. Such a value can be allocated on a heap with
    /// `heap.alloc(StarlarkAny::new(x))`.
    pub fn new(x: T) -> Self {
        StarlarkAny(x)
    }

    /// Extract from a [`Value`] that contains a [`StarlarkAny`] underneath. Returns [`None`] if
    /// the value does not match the expected type.
    pub fn get<'v>(x: Value<'v>) -> Option<&'v T> {
        let x: &StarlarkAny<T> = x.downcast_ref()?;
        Some(&x.0)
    }
}

impl FrozenHeap {
    /// Allocate any value in the frozen heap.
    pub fn alloc_any<T: StarlarkAnyBound>(&self, value: T) -> FrozenRef<'static, T> {
        self.alloc_simple_typed_static(StarlarkAny::new(value))
            .as_frozen_ref()
            .map(|r| &r.0)
    }
}

/// Marker trait for types that can be wrapped in `StarlarkAny`
/// and are registered for vtable lookup.
///
/// # Safety
///
/// Implementors must also register the vtable entry for `StarlarkAny<Self>`
/// using [`register_simple_vtable_entry!`]. Use the [`register_starlark_any!`]
/// macro instead of implementing this trait manually, as it handles both the trait
/// implementation and vtable registration.
pub unsafe trait StarlarkAnyRegistered {}

/// Trait alias that captures the bounds required for types wrapped in `StarlarkAny`.
///
/// When the `pagable` feature is enabled, this includes `StarlarkAnyRegistered`.
#[cfg(feature = "pagable")]
pub trait StarlarkAnyBound: Debug + Send + Sync + 'static + StarlarkAnyRegistered {}

#[cfg(feature = "pagable")]
impl<T: Debug + Send + Sync + 'static + StarlarkAnyRegistered> StarlarkAnyBound for T {}

/// Trait alias that captures the bounds required for types wrapped in `StarlarkAny`.
#[cfg(not(feature = "pagable"))]
pub trait StarlarkAnyBound: Debug + Send + Sync + 'static {}

#[cfg(not(feature = "pagable"))]
impl<T: Debug + Send + Sync + 'static> StarlarkAnyBound for T {}

#[cfg(feature = "pagable")]
unsafe impl<T: StarlarkAnyBound> VtableRegistered for StarlarkAny<T> {}

#[cfg(not(feature = "pagable"))]
unsafe impl<T: StarlarkAnyBound> VtableRegistered for StarlarkAny<T> {}

/// Typed reference to a `T` allocated via [`StarlarkAny<T>`] on a frozen heap.
///
/// Implemented as a newtype rather than a type alias for
/// `FrozenValueTyped<'static, StarlarkAny<T>>` so we can define our own
/// `Display`, `Debug`, `Deref`, and `BcInstrArg` trait impls that delegate
/// to `T`. With a type alias, the existing impls on `FrozenValueTyped`
/// would apply — including the `BcInstrArg` trait impl for
/// `FrozenValueTyped<T>` — and all of them go through the Starlark value
/// repr, printing `<any>` instead of the inner value.
///
/// Specifically, the newtype provides:
/// - `Deref` trait with `Target = T` directly to the inner value (skipping `StarlarkAny`)
/// - `Display` trait delegating to `T::Display` (not the Starlark `<any>` repr)
/// - `Debug` trait delegating to `T::Debug`
#[derive(Allocative, Copy_, Clone_, Dupe_)]
#[allocative(skip)]
pub struct FrozenAnyValue<T: Debug + Send + Sync + 'static>(
    FrozenValueTyped<'static, StarlarkAny<T>>,
);

impl<T: Debug + Send + Sync + 'static> Debug for FrozenAnyValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.as_ref(), f)
    }
}

impl<T: Debug + Display + Send + Sync + 'static> Display for FrozenAnyValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self.as_ref(), f)
    }
}

impl<T: Debug + Send + Sync + 'static> Deref for FrozenAnyValue<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T: Debug + Send + Sync + 'static + PartialEq> PartialEq for FrozenAnyValue<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}
impl<T: Debug + Send + Sync + 'static + Eq> Eq for FrozenAnyValue<T> {}

unsafe impl<'v, T: Debug + Send + Sync + 'static> Trace<'v> for FrozenAnyValue<T> {
    fn trace(&mut self, _: &Tracer<'v>) {}
}

impl<T: Debug + Send + Sync + 'static> Freeze for FrozenAnyValue<T> {
    type Frozen = Self;

    fn freeze(self, _freezer: &Freezer) -> FreezeResult<Self::Frozen> {
        Ok(self)
    }
}

impl<T: Debug + Send + Sync + 'static> FrozenAnyValue<T> {
    /// Get a reference to the inner value with `'static` lifetime.
    #[inline]
    pub fn as_ref(&self) -> &'static T {
        &self.0.as_ref().0
    }

    /// Convert to the underlying `FrozenValue`.
    #[inline]
    pub fn to_frozen_value(self) -> FrozenValue {
        self.0.to_frozen_value()
    }

    /// Wrap a `FrozenValueTyped<StarlarkAny<T>>`.
    #[inline]
    pub(crate) fn from_typed(typed: FrozenValueTyped<'static, StarlarkAny<T>>) -> Self {
        FrozenAnyValue(typed)
    }

    /// Construct from a raw `FrozenValue` without type checking.
    ///
    /// # Safety
    /// The caller must ensure the value is a `StarlarkAny<T>`.
    #[expect(dead_code)] // Used starting from diff 4.
    #[inline]
    pub(crate) unsafe fn new_unchecked(value: FrozenValue) -> Self {
        // SAFETY: caller guarantees value is a StarlarkAny<T>.
        FrozenAnyValue(unsafe { FrozenValueTyped::new_unchecked(value) })
    }
}

impl FrozenHeap {
    /// Allocate any value on the frozen heap, returning a [`FrozenAnyValue`].
    pub fn alloc_any_value<T: StarlarkAnyBound>(&self, value: T) -> FrozenAnyValue<T> {
        FrozenAnyValue::from_typed(self.alloc_simple_typed_static(StarlarkAny::new(value)))
    }
}
