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
//!   and deconstructed from a [`Value`] with
//! * To define your own Rust data type that can live in a [`Value`] it must implement the [`StarlarkValue`]
//!   trait.
//! * All the nested modules represent the built-in Starlark values. These are all defined using [`StarlarkValue`],
//!   so may serve as interesting inspiration for writing your own values, in addition to occuring in Starlark programs.
pub use crate::values::{error::*, iter::*, layout::*, owned::*, traits::*, types::*, unpack::*};
use crate::{
    codemap::Span,
    collections::{Hashed, SmallHashResult},
    eval::{Evaluator, Parameters},
    values::{function::FUNCTION_TYPE, types::function::FunctionInvoker},
};
pub use gazebo::{any::AnyLifetime, cell::ARef, prelude::*};
use indexmap::Equivalent;
use std::{
    cell::RefMut,
    cmp::Ordering,
    fmt,
    fmt::{Debug, Display},
};

#[macro_use]
mod comparison;

// Submodules
mod error;
pub(crate) mod fast_string;
mod index;
mod interpolation;
mod iter;
mod layout;
mod owned;
mod stack_guard;
mod traits;
mod types;
mod typing;
mod unpack;

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
    f.debug_tuple(typ).field(v.get_aref().as_debug()).finish()
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
        let v: Value = Value::new_frozen(*self);
        let other: Value = Value::new_frozen(*other);
        v.equals(other).ok() == Some(true)
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

/// Trait for things that can be allocated on a [`Heap`] producing a [`Value`].
pub trait AllocValue<'v> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v>;
}

impl<'v> AllocValue<'v> for Value<'v> {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        self
    }
}

/// Trait for things that can be allocated on a [`FrozenHeap`] producing a [`FrozenValue`].
pub trait AllocFrozenValue {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue;
}

impl FrozenHeap {
    /// Allocate a new value on a [`FrozenHeap`].
    pub fn alloc<T: AllocFrozenValue>(&self, val: T) -> FrozenValue {
        val.alloc_frozen_value(self)
    }
}

impl Heap {
    /// Allocate a new value on a [`Heap`].
    pub fn alloc<'v, T: AllocValue<'v>>(&'v self, x: T) -> Value<'v> {
        x.alloc_value(self)
    }
}

/// Abstract over [`Value`] and [`FrozenValue`].
///
/// The methods on this trait are those required to implement containers,
/// allowing implementations of [`ComplexValue`] to be agnostic of their contained type.
/// For details about each function, see the documentation for [`Value`],
/// which provides the same functions (and more).
pub trait ValueLike<'v>: Eq + Copy + Debug {
    /// Produce a [`Value`] regardless of the type you are starting with.
    fn to_value(self) -> Value<'v>;

    fn get_aref(self) -> ARef<'v, dyn StarlarkValue<'v>>;

    fn new_invoker(self, eval: &mut Evaluator<'v, '_>) -> anyhow::Result<FunctionInvoker<'v>> {
        self.to_value().new_invoker(eval)
    }

    fn invoke(
        self,
        location: Option<Span>,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        self.to_value().invoke(location, params, eval)
    }

    fn get_hash(self) -> anyhow::Result<u64> {
        self.get_aref().get_hash()
    }

    fn get_hashed(self) -> anyhow::Result<Hashed<Self>> {
        Ok(Hashed::new_unchecked(
            SmallHashResult::new_unchecked(self.get_hash()?),
            self,
        ))
    }

    fn collect_repr(self, collector: &mut String) {
        self.get_aref().collect_repr(collector);
    }

    fn to_json(self) -> anyhow::Result<String> {
        self.get_aref().to_json()
    }

    fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        if self.to_value().ptr_eq(other) {
            Ok(true)
        } else {
            let _guard = stack_guard::stack_guard()?;
            self.get_aref().equals(other)
        }
    }

    fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        let _guard = stack_guard::stack_guard()?;
        self.get_aref().compare(other)
    }

    fn downcast_ref<T: AnyLifetime<'v>>(self) -> Option<ARef<'v, T>> {
        let any = ARef::map(self.get_aref(), |e| e.as_dyn_any());
        if any.is::<T>() {
            Some(ARef::map(any, |any| any.downcast_ref::<T>().unwrap()))
        } else {
            None
        }
    }
}

impl<'v, V: ValueLike<'v>> Hashed<V> {
    pub(crate) fn to_hashed_value(&self) -> Hashed<Value<'v>> {
        // Safe because we know frozen values have the same hash as non-frozen ones
        Hashed::new_unchecked(self.hash(), self.key().to_value())
    }
}

impl<'v> Hashed<Value<'v>> {
    fn freeze(&self, freezer: &Freezer) -> Hashed<FrozenValue> {
        // Safe because we know frozen values have the same hash as non-frozen ones
        let key = self.key().freeze(freezer);
        // But it's an easy mistake to make, so actually check it in debug
        debug_assert_eq!(Some(self.hash()), key.get_hashed().ok().map(|x| x.hash()));
        Hashed::new_unchecked(self.hash(), key)
    }
}

impl<'v> ValueLike<'v> for Value<'v> {
    fn get_aref(self) -> ARef<'v, dyn StarlarkValue<'v>> {
        Value::get_aref(self)
    }

    fn to_value(self) -> Value<'v> {
        self
    }
}

impl<'v> ValueLike<'v> for FrozenValue {
    fn get_aref(self) -> ARef<'v, dyn StarlarkValue<'v>> {
        ARef::new_ptr(self.get_ref())
    }

    fn to_value(self) -> Value<'v> {
        Value::new_frozen(self)
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
        if let Some(v) = other.get_aref().radd(me, heap) {
            v
        } else {
            self.get_aref().add(other, heap)
        }
    }

    /// Convert a value to a [`FrozenValue`] using a supplied [`Freezer`].
    pub fn freeze(self, freezer: &Freezer) -> FrozenValue {
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

    /// Forwards to [`ComplexValue::set_attr`].
    pub fn set_attr(
        self,
        attribute: &str,
        alloc_value: Value<'v>,
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        self.get_ref_mut(heap)?.set_attr(attribute, alloc_value)
    }

    /// Forwards to [`ComplexValue::set_at`].
    pub fn set_at(
        self,
        index: Value<'v>,
        alloc_value: Value<'v>,
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        self.get_ref_mut(heap)?.set_at(index, alloc_value)
    }

    /// Return the contents of an iterable collection, as an owned vector.
    pub fn iterate_collect(self, heap: &'v Heap) -> anyhow::Result<Vec<Value<'v>>> {
        // You might reasonably think this is mostly called on lists (I think it is),
        // and thus that a fast-path here would speed things up. But in my experiments
        // it's completely irrelevant (you pay a bit for the check, you save a bit on each step).
        Ok(self.iterate(heap)?.iter().collect())
    }

    /// Produce an iterable from a value.
    pub fn iterate(self, heap: &'v Heap) -> anyhow::Result<RefIterable<'v>> {
        let me: ARef<'v, dyn StarlarkValue> = self.get_aref();
        me.iterate()?;
        Ok(RefIterable::new(
            heap,
            ARef::map(me, |e| e.iterate().unwrap()),
        ))
    }

    /// Get the [`Hashed`] version of this [`Value`].
    pub fn get_hashed(self) -> anyhow::Result<Hashed<Self>> {
        ValueLike::get_hashed(self)
    }

    /// Get a reference to underlying data or [`None`]
    /// if contained object has different type than requested.
    ///
    /// This function panics if the [`Value`] is borrowed mutably.
    ///
    /// In many cases you may wish to call [`FromValue`] instead, as that can
    /// get a non-frozen value from an underlying frozen value.
    pub fn downcast_ref<T: AnyLifetime<'v>>(self) -> Option<ARef<'v, T>> {
        ValueLike::downcast_ref(self)
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

    /// Get a mutable reference to underlying data or [`None`]
    /// if contained object has different type than requested.
    ///
    /// This function returns an [`Err`] if the [`Value`] is already borrowed, is frozen,
    /// or frozen for iteration.
    ///
    /// While this reference is active, any [`get_aref`](Value::get_aref) or similar on the value will
    /// _cause a panic_. Therefore, it's super important not to call any Starlark operations,
    /// even as simple as equality, while holding the [`RefMut`].
    pub fn downcast_mut<T: AnyLifetime<'v>>(
        self,
        heap: &'v Heap,
    ) -> anyhow::Result<Option<RefMut<'_, T>>> {
        let vref = self.get_ref_mut(heap)?;
        let any: RefMut<'_, dyn AnyLifetime<'v>> = RefMut::map(vref, |v| v.as_dyn_any_mut());
        Ok(if any.is::<T>() {
            Some(RefMut::map(any, |any| any.downcast_mut::<T>().unwrap()))
        } else {
            None
        })
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
    pub fn export_as(self, name: &str, heap: &'v Heap) {
        if let Some(mut mv) = self.get_ref_mut_already() {
            mv.export_as(heap, name)
        }
    }

    /// Return the attribute with the given name. Returns a pair of a boolean and the value.
    ///
    /// The type is [`AttrType::Method`] if the attribute was defined via [`StarlarkValue::get_methods`]
    /// and should be used as a signal that if the attribute is subsequently called,
    /// e.g. `object.attribute(argument)` then the `object` should be passed as the first
    /// argument to the function, e.g. `object.attribute(object, argument)`.
    pub fn get_attr(
        self,
        attribute: &str,
        heap: &'v Heap,
    ) -> anyhow::Result<(AttrType, Value<'v>)> {
        let aref = self.get_aref();
        if let Some(methods) = aref.get_methods() {
            if let Some(v) = methods.get(attribute) {
                return Ok((AttrType::Method, v));
            }
        }
        aref.get_attr(attribute, heap).map(|v| (AttrType::Field, v))
    }

    /// Query whether an attribute exists on a type. Should be equivalent to whether
    /// [`get_attr`](Value::get_attr) succeeds, but potentially more efficient.
    pub fn has_attr(self, attribute: &str) -> bool {
        let aref = self.get_aref();
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
        let aref = self.get_aref();
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
        self.get_aref().get_type()
    }
    pub fn to_bool(self) -> bool {
        // Fast path for the common case
        if let Some(x) = self.unpack_bool() {
            x
        } else {
            self.get_aref().to_bool()
        }
    }
    pub fn to_int(self) -> anyhow::Result<i32> {
        // Fast path for the common case
        if let Some(x) = self.unpack_int() {
            Ok(x)
        } else {
            self.get_aref().to_int()
        }
    }
    pub fn at(self, index: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().at(index, heap)
    }

    pub fn slice(
        self,
        start: Option<Value<'v>>,
        stop: Option<Value<'v>>,
        stride: Option<Value<'v>>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        self.get_aref().slice(start, stop, stride, heap)
    }

    pub fn length(self) -> anyhow::Result<i32> {
        self.get_aref().length()
    }

    pub fn is_in(self, other: Value<'v>) -> anyhow::Result<bool> {
        self.get_aref().is_in(other)
    }

    pub fn plus(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().plus(heap)
    }

    pub fn minus(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().minus(heap)
    }

    pub fn sub(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().sub(other, heap)
    }

    pub fn mul(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().mul(other, heap)
    }

    pub fn percent(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().percent(other, heap)
    }

    pub fn floor_div(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().floor_div(other, heap)
    }

    pub fn bit_and(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_aref().bit_and(other)
    }
    pub fn bit_or(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_aref().bit_or(other)
    }
    pub fn bit_xor(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_aref().bit_xor(other)
    }
    pub fn left_shift(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_aref().left_shift(other)
    }
    pub fn right_shift(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_aref().right_shift(other)
    }

    pub fn new_invoker(self, eval: &mut Evaluator<'v, '_>) -> anyhow::Result<FunctionInvoker<'v>> {
        self.get_aref().new_invoker(self, eval)
    }

    pub fn invoke(
        self,
        location: Option<Span>,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        self.get_aref().invoke(self, location, params, eval)
    }

    /// Invoke a function with only positional arguments.
    pub fn invoke_pos(
        self,
        location: Option<Span>,
        pos: &[Value<'v>],
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let params = Parameters {
            pos,
            ..Parameters::default()
        };
        self.invoke(location, params, eval)
    }

    pub fn get_type_value(self) -> &'static ConstFrozenValue {
        self.get_aref().get_type_value()
    }
}
