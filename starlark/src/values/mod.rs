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

//! Defines a runtime Starlark value ([`Value`]) and traits for defining custom values ([`StarlarkValue`]).
//!
//! This module contains code for working with Starlark values:
//!
//! * Most code dealing with Starlark will use [`Value`], as it represents the fundamental values used in
//!   Starlark. When frozen, they become [`FrozenValue`].
//! * Values are garbage-collected, so a given [`Value`] lives on a [`Heap`].
//! * Rust values (e.g. [`String`], [`Vec`]) can be added to the [`Heap`] with [`AllocValue`],
//!   and deconstructed from a [`Value`] with [`FromValue`] (or specialised methods like [`unpack_str`](Value::unpack_str)).
//! * To define your own Rust data type that can live in a [`Value`] it must implement the [`StarlarkValue`]
//!   trait.
//! * All the nested modules represent the built-in Starlark values. These are all defined using [`StarlarkValue`],
//!   so may serve as interesting inspiration for writing your own values, in addition to occuring in Starlark programs.
pub use crate::values::{
    alloc_value::*, error::*, frozen_ref::*, layout::*, owned::*, traits::*, types::*, unpack::*,
};
use crate::{
    codemap::Span,
    collections::{Hashed, SmallHashResult},
    eval::{Arguments, Evaluator},
    values::function::FUNCTION_TYPE,
};
use gazebo::coerce::CoerceKey;
pub use gazebo::{any::AnyLifetime, cell::ARef, coerce::Coerce, prelude::*};
use indexmap::Equivalent;
pub use starlark_derive::{starlark_attrs, StarlarkAttrs, Trace};
use std::{
    cmp::Ordering,
    fmt,
    fmt::{Debug, Display},
};

#[macro_use]
mod comparison;

// Submodules
mod alloc_value;
pub mod docs;
mod error;
pub(crate) mod fast_string;
mod frozen_ref;
mod index;
pub(crate) mod interpolation;
pub(crate) mod iter;
mod layout;
mod owned;
mod stack_guard;
mod traits;
mod types;
pub(crate) mod typing;
mod unpack;

unsafe impl<'v> Coerce<Value<'v>> for FrozenValue {}
unsafe impl<'v> CoerceKey<Value<'v>> for FrozenValue {}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl Display for FrozenValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Value::new_frozen(*self).to_str())
    }
}

fn debug_value(typ: &str, v: Value, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_tuple(typ).field(v.get_ref().as_debug()).finish()
}

impl Debug for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug_value("Value", *self, f)
    }
}

impl Debug for FrozenValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug_value("FrozenValue", Value::new_frozen(*self), f)
    }
}

impl<'v> PartialEq for Value<'v> {
    fn eq(&self, other: &Value<'v>) -> bool {
        self.equals(*other).ok() == Some(true)
    }
}

impl PartialEq for FrozenValue {
    fn eq(&self, other: &FrozenValue) -> bool {
        self.to_value().eq(&other.to_value())
    }
}

impl Eq for Value<'_> {}

impl Eq for FrozenValue {}

impl Equivalent<FrozenValue> for Value<'_> {
    fn equivalent(&self, key: &FrozenValue) -> bool {
        key.equals(*self).unwrap()
    }
}

impl Equivalent<Value<'_>> for FrozenValue {
    fn equivalent(&self, key: &Value) -> bool {
        self.equals(*key).unwrap()
    }
}

/// Abstract over [`Value`] and [`FrozenValue`].
///
/// The methods on this trait are those required to implement containers,
/// allowing implementations of [`ComplexValue`] to be agnostic of their contained type.
/// For details about each function, see the documentation for [`Value`],
/// which provides the same functions (and more).
pub trait ValueLike<'v>: Eq + Copy + Debug + Default + CoerceKey<Value<'v>> {
    /// Produce a [`Value`] regardless of the type you are starting with.
    fn to_value(self) -> Value<'v>;

    /// Get referenced [`StarlarkValue`] a value as [`AnyLifetime`].
    fn as_dyn_any(self) -> &'v dyn AnyLifetime<'v>;

    fn invoke(
        self,
        location: Option<Span>,
        args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        self.to_value().invoke(location, args, eval)
    }

    fn get_hash(self) -> anyhow::Result<u64>;

    fn get_hashed(self) -> anyhow::Result<Hashed<Self>> {
        Ok(Hashed::new_unchecked(
            SmallHashResult::new_unchecked(self.get_hash()?),
            self,
        ))
    }

    fn collect_repr(self, collector: &mut String);

    fn to_json(self) -> anyhow::Result<String>;

    fn equals(self, other: Value<'v>) -> anyhow::Result<bool>;

    fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering>;

    /// Get a reference to underlying data or [`None`]
    /// if contained object has different type than requested.
    fn downcast_ref<T: StarlarkValue<'v>>(self) -> Option<&'v T>;
}

impl<'v, V: ValueLike<'v>> Hashed<V> {
    pub(crate) fn to_hashed_value(&self) -> Hashed<Value<'v>> {
        // Safe because we know frozen values have the same hash as non-frozen ones
        Hashed::new_unchecked(self.hash(), self.key().to_value())
    }
}

impl<'v> Hashed<Value<'v>> {
    pub(crate) fn freeze(&self, freezer: &Freezer) -> anyhow::Result<Hashed<FrozenValue>> {
        // Safe because we know frozen values have the same hash as non-frozen ones
        let key = self.key().freeze(freezer)?;
        // But it's an easy mistake to make, so actually check it in debug
        debug_assert_eq!(Some(self.hash()), key.get_hashed().ok().map(|x| x.hash()));
        Ok(Hashed::new_unchecked(self.hash(), key))
    }
}

impl Default for Value<'_> {
    fn default() -> Self {
        Self::new_none()
    }
}

impl Default for FrozenValue {
    fn default() -> Self {
        Self::new_none()
    }
}

impl<'v> ValueLike<'v> for Value<'v> {
    fn to_value(self) -> Value<'v> {
        self
    }

    fn downcast_ref<T: StarlarkValue<'v>>(self) -> Option<&'v T> {
        self.get_ref().downcast_ref::<T>()
    }

    fn collect_repr(self, collector: &mut String) {
        self.get_ref().collect_repr(collector);
    }

    fn get_hash(self) -> anyhow::Result<u64> {
        self.get_ref().get_hash()
    }

    fn to_json(self) -> anyhow::Result<String> {
        self.get_ref().to_json()
    }

    fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        if self.ptr_eq(other) {
            Ok(true)
        } else {
            let _guard = stack_guard::stack_guard()?;
            self.get_ref().equals(other)
        }
    }

    fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        let _guard = stack_guard::stack_guard()?;
        self.get_ref().compare(other)
    }

    fn as_dyn_any(self) -> &'v dyn AnyLifetime<'v> {
        self.get_ref().value_as_dyn_any()
    }
}

impl<'v> ValueLike<'v> for FrozenValue {
    fn to_value(self) -> Value<'v> {
        Value::new_frozen(self)
    }

    fn downcast_ref<T: StarlarkValue<'v>>(self) -> Option<&'v T> {
        self.to_value().downcast_ref()
    }

    fn collect_repr(self, collector: &mut String) {
        self.to_value().collect_repr(collector)
    }

    fn get_hash(self) -> anyhow::Result<u64> {
        self.to_value().get_hash()
    }

    fn to_json(self) -> anyhow::Result<String> {
        self.to_value().to_json()
    }

    fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        self.to_value().equals(other)
    }

    fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        self.to_value().compare(other)
    }

    fn as_dyn_any(self) -> &'v dyn AnyLifetime<'v> {
        self.get_ref().value_as_dyn_any()
    }
}

impl FrozenValue {
    /// Convert a [`FrozenValue`] back to a [`Value`].
    pub fn to_value<'v>(self) -> Value<'v> {
        Value::new_frozen(self)
    }
}

/// How an attribute (e.g. `x.f`) should behave.
#[derive(Clone, Copy, Dupe, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum AttrType {
    /// The attribute is a field, a direct value with no special behaviour.
    Field,
    /// The attribute is a method, which should be called passing the `x` value
    /// as its first argument. It will either be a function (which is transformed
    /// into a [`BoundMethod`](crate::values::function::BoundMethod)) or a
    /// [`NativeAttribute`](crate::values::function::NativeAttribute)
    /// (which is evaluated immediately).
    Method,
}

impl<'v> Value<'v> {
    /// Add two [`Value`]s together. Will first try using [`radd`](StarlarkValue::radd),
    /// before falling back to [`add`](StarlarkValue::add).
    pub fn add(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let me = self.to_value();
        if let Some(v) = other.get_ref().radd(me, heap) {
            v
        } else {
            self.get_ref().add(other, heap)
        }
    }

    /// Convert a value to a [`FrozenValue`] using a supplied [`Freezer`].
    pub fn freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenValue> {
        freezer.freeze(self)
    }

    /// Implement the `str()` function - converts a string value to itself,
    /// otherwise uses `repr()`.
    pub fn to_str(self) -> String {
        match self.unpack_str() {
            None => self.to_repr(),
            Some(s) => s.to_owned(),
        }
    }

    /// Implement the `repr()` function.
    pub fn to_repr(self) -> String {
        let mut s = String::new();
        self.collect_repr(&mut s);
        s
    }

    /// Forwards to [`StarlarkValue::set_attr`].
    pub fn set_attr(self, attribute: &str, alloc_value: Value<'v>) -> anyhow::Result<()> {
        self.get_ref().set_attr(attribute, alloc_value)
    }

    /// Forwards to [`StarlarkValue::set_at`].
    pub fn set_at(self, index: Value<'v>, alloc_value: Value<'v>) -> anyhow::Result<()> {
        self.get_ref().set_at(index, alloc_value)
    }

    /// Return the contents of an iterable collection, as an owned vector.
    pub fn iterate_collect(self, heap: &'v Heap) -> anyhow::Result<Vec<Value<'v>>> {
        // You might reasonably think this is mostly called on lists (I think it is),
        // and thus that a fast-path here would speed things up. But in my experiments
        // it's completely irrelevant (you pay a bit for the check, you save a bit on each step).
        self.with_iterator(heap, |it| it.collect())
    }

    /// Operate over an iterable for a value.
    pub fn with_iterator<T>(
        self,
        heap: &'v Heap,
        mut f: impl FnMut(&mut dyn Iterator<Item = Value<'v>>) -> T,
    ) -> anyhow::Result<T> {
        let mut res = None;
        self.get_ref().with_iterator(heap, &mut |it| {
            res = Some(f(it));
            Ok(())
        })?;
        // Safe because if we ran the iterator, we should have called it and set `res`
        Ok(res.take().expect("with_iterator to call the callback"))
    }

    /// Produce an iterable from a value.
    pub fn iterate(
        self,
        heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'v>> {
        self.get_ref().iterate(heap)
    }

    /// Get the [`Hashed`] version of this [`Value`].
    pub fn get_hashed(self) -> anyhow::Result<Hashed<Self>> {
        ValueLike::get_hashed(self)
    }

    /// Are two values equal. If the values are of different types it will
    /// return [`false`]. It will only error if there is excessive recursion.
    pub fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        ValueLike::equals(self, other)
    }

    /// How are two values comparable. For values of different types will return [`Err`].
    pub fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        ValueLike::compare(self, other)
    }

    /// Describe the value, in order to get its metadata in a way that could be used
    /// to generate prototypes, help information or whatever other descriptive text
    /// is required.
    /// Plan is to make this return a data type at some point in the future, possibly
    /// move on to `StarlarkValue` and include data from members.
    pub fn describe(self, name: &str) -> String {
        if self.get_type() == FUNCTION_TYPE {
            format!("def {}: pass", self.to_repr().replace(" = ...", " = None"))
        } else {
            format!("# {} = {}", name, self.to_repr())
        }
    }

    /// Call `export_as` on the underlying value, but only if the type is mutable.
    /// Otherwise, does nothing.
    pub fn export_as(self, variable_name: &str, eval: &mut Evaluator<'v, '_>) {
        self.get_ref().export_as(variable_name, eval)
    }

    /// Return the attribute with the given name. Returns a pair of a boolean and the value.
    ///
    /// The type is [`AttrType::Method`] if the attribute was defined via [`StarlarkValue::get_methods`]
    /// and should be used as a signal that if the attribute is subsequently called,
    /// e.g. `object.attribute(argument)` then the `object` should be passed as the first
    /// argument to the function, e.g. `object.attribute(object, argument)`.
    pub fn get_attr(self, attribute: &str, heap: &'v Heap) -> Option<(AttrType, Value<'v>)> {
        let aref = self.get_ref();
        if let Some(methods) = aref.get_methods() {
            if let Some(v) = methods.get(attribute) {
                return Some((AttrType::Method, v));
            }
        }
        aref.get_attr(attribute, heap).map(|v| (AttrType::Field, v))
    }

    /// Like `get_attr` but return an error if the attribute is not available.
    pub fn get_attr_error(
        self,
        attribute: &str,
        heap: &'v Heap,
    ) -> anyhow::Result<(AttrType, Value<'v>)> {
        match self.get_attr(attribute, heap) {
            None => {
                ValueError::unsupported_owned(self.get_type(), &format!(".{}", attribute), None)
            }
            Some(x) => Ok(x),
        }
    }

    /// Query whether an attribute exists on a type. Should be equivalent to whether
    /// [`get_attr`](Value::get_attr) succeeds, but potentially more efficient.
    pub fn has_attr(self, attribute: &str) -> bool {
        let aref = self.get_ref();
        if let Some(methods) = aref.get_methods() {
            if methods.get(attribute).is_some() {
                return true;
            }
        }
        aref.has_attr(attribute)
    }

    /// Get a list of all the attributes this function supports, used to implement the
    /// `dir()` function.
    pub fn dir_attr(self) -> Vec<String> {
        let aref = self.get_ref();
        let mut result = if let Some(methods) = aref.get_methods() {
            let mut res = methods.names();
            res.extend(aref.dir_attr());
            res
        } else {
            aref.dir_attr()
        };
        result.sort();
        result
    }
}

/// Methods that just forward to the underlying [`StarlarkValue`].
impl<'v> Value<'v> {
    pub fn get_type(self) -> &'static str {
        self.get_ref().get_type()
    }
    pub fn to_bool(self) -> bool {
        // Fast path for the common case
        if let Some(x) = self.unpack_bool() {
            x
        } else {
            self.get_ref().to_bool()
        }
    }
    pub fn to_int(self) -> anyhow::Result<i32> {
        // Fast path for the common case
        if let Some(x) = self.unpack_int() {
            Ok(x)
        } else {
            self.get_ref().to_int()
        }
    }
    pub fn at(self, index: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().at(index, heap)
    }

    pub fn slice(
        self,
        start: Option<Value<'v>>,
        stop: Option<Value<'v>>,
        stride: Option<Value<'v>>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        self.get_ref().slice(start, stop, stride, heap)
    }

    pub fn length(self) -> anyhow::Result<i32> {
        self.get_ref().length()
    }

    pub fn is_in(self, other: Value<'v>) -> anyhow::Result<bool> {
        self.get_ref().is_in(other)
    }

    pub fn plus(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().plus(heap)
    }

    pub fn minus(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().minus(heap)
    }

    pub fn sub(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().sub(other, heap)
    }

    pub fn mul(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().mul(other, heap)
    }

    pub fn percent(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().percent(other, heap)
    }

    pub fn floor_div(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_ref().floor_div(other, heap)
    }

    pub fn bit_and(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_ref().bit_and(other)
    }
    pub fn bit_or(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_ref().bit_or(other)
    }
    pub fn bit_xor(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_ref().bit_xor(other)
    }
    pub fn left_shift(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_ref().left_shift(other)
    }
    pub fn right_shift(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_ref().right_shift(other)
    }

    pub fn invoke(
        self,
        location: Option<Span>,
        args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        self.get_ref().invoke(self, location, args, eval)
    }

    /// Invoke a function with only positional arguments.
    pub fn invoke_pos(
        self,
        location: Option<Span>,
        pos: &[Value<'v>],
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let params = Arguments {
            pos,
            ..Arguments::default()
        };
        self.invoke(location, params, eval)
    }

    pub fn get_type_value(self) -> FrozenStringValue {
        self.get_ref().get_type_value()
    }
}
