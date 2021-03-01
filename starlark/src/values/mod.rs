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

//! The values module define a trait `TypedValue` that defines the attribute of
//! any value in Starlark and a few macro to help implementing this trait.
//! The `Value` struct defines the actual structure holding a TypedValue. It is
//! mostly used to enable mutable and Rc behavior over a TypedValue.
//! This modules also defines this traits for the basic immutable values: int,
//! bool and NoneType. Sub-modules implement other common types of all Starlark
//! dialect.
//!
//! __Note__: we use _sequence_, _iterable_ and _indexable_ according to the
//! definition in the [Starlark specification](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#sequence-types).
//! We also use the term _container_ for denoting any of those type that can
//! hold several values.
pub use crate::values::{
    error::*, interpolation::*, iter::*, layout::*, owned::*, traits::*, types::*,
};
use crate::{
    collections::{Hashed, SmallHashResult},
    values::types::function::FunctionInvoker,
};
use gazebo::{any::AnyLifetime, cell::ARef};
use indexmap::Equivalent;
use std::{
    cell::RefMut,
    cmp::Ordering,
    fmt,
    fmt::{Debug, Display},
    mem,
};

#[macro_use]
mod comparison;

// Submodules
mod error;
mod fast_string;
mod index;
mod interpolation;
mod iter;
mod layout;
mod owned;
mod traits;
mod types;
mod typing;

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
    if v.is_unassigned() {
        f.write_str(typ)?;
        f.write_str("::Unassigned")
    } else {
        f.debug_tuple(typ).field(v.get_aref().as_debug()).finish()
    }
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

pub trait AllocValue<'v> {
    /// Everything can either be a literal, mutable or immutable.
    fn alloc_value(self, heap: &'v Heap) -> Value<'v>;
}

impl<'v> AllocValue<'v> for Value<'v> {
    fn alloc_value(self, _heap: &'v Heap) -> Value<'v> {
        self
    }
}

pub trait AllocFrozenValue<'v> {
    fn alloc_frozen_value(self, heap: &'v FrozenHeap) -> FrozenValue;
}

impl FrozenHeap {
    pub fn alloc<'v, T: AllocFrozenValue<'v>>(&'v self, val: T) -> FrozenValue {
        val.alloc_frozen_value(self)
    }
}

impl Heap {
    pub fn alloc<'v, T: AllocValue<'v>>(&'v self, x: T) -> Value<'v> {
        x.alloc_value(self)
    }
}

/// Implemented for `Value` and `FrozenValue`.
pub trait ValueLike<'v>: Eq + Copy + Debug {
    fn to_value(self) -> Value<'v>;

    fn get_aref(self) -> ARef<'v, dyn TypedValue<'v>>;

    fn new_invoker(self, heap: &'v Heap) -> anyhow::Result<FunctionInvoker<'v, '_>>;

    fn as_any_ref(self) -> ARef<'v, dyn AnyLifetime<'v>> {
        ARef::map(self.get_aref(), |e| e.as_dyn_any())
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
    fn to_json(self) -> String {
        self.get_aref().to_json()
    }

    fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        let _guard = crate::eval::call_stack::try_inc()?;
        if self.to_value().ptr_eq(other) {
            Ok(true)
        } else {
            self.get_aref().equals(other)
        }
    }

    fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        let _guard = crate::eval::call_stack::try_inc()?;
        self.get_aref().compare(other)
    }

    /// Get a reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed mutably.
    fn downcast_ref<T: AnyLifetime<'v>>(self) -> Option<ARef<'v, T>> {
        let any = self.as_any_ref();
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
        Hashed::new_unchecked(self.hash(), self.key().freeze(freezer))
    }
}

impl<'v> ValueLike<'v> for Value<'v> {
    fn get_aref(self) -> ARef<'v, dyn TypedValue<'v>> {
        Value::get_aref(self)
    }

    fn to_value(self) -> Value<'v> {
        self
    }

    fn new_invoker(self, heap: &'v Heap) -> anyhow::Result<FunctionInvoker<'v, '_>> {
        self.new_invoker(heap)
    }
}

impl<'v> ValueLike<'v> for FrozenValue {
    fn get_aref(self) -> ARef<'v, dyn TypedValue<'v>> {
        ARef::Ptr(self.get_ref())
    }

    fn to_value(self) -> Value<'v> {
        Value::new_frozen(self)
    }

    fn new_invoker(self, heap: &'v Heap) -> anyhow::Result<FunctionInvoker<'v, '_>> {
        self.get_ref().new_invoker(self.to_value(), heap)
    }
}

impl FrozenValue {
    pub fn to_value<'v>(self) -> Value<'v> {
        Value::new_frozen(self)
    }
}

impl<'v> Value<'v> {
    pub fn get_type(self) -> &'static str {
        self.get_aref().get_type()
    }
    pub fn to_bool(self) -> bool {
        self.get_aref().to_bool()
    }
    pub fn to_int(self) -> anyhow::Result<i32> {
        self.get_aref().to_int()
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

    pub fn get_attr(self, attribute: &str, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.get_aref().get_attr(attribute, heap)
    }

    pub fn has_attr(self, attribute: &str) -> bool {
        self.get_aref().has_attr(attribute)
    }

    pub fn dir_attr(self) -> Vec<String> {
        self.get_aref().dir_attr()
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

    pub fn add(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let me = self.to_value();
        if let Some(v) = other.get_aref().radd(other, me, heap) {
            v
        } else {
            self.get_aref().add(me, other, heap)
        }
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

    pub fn pipe(self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.get_aref().pipe(other)
    }

    pub fn freeze(self, freezer: &Freezer) -> FrozenValue {
        freezer.freeze(self)
    }

    pub fn to_str(self) -> String {
        match self.unpack_str() {
            None => self.to_repr(),
            Some(s) => s.to_owned(),
        }
    }

    pub fn set_attr(
        self,
        attribute: &str,
        alloc_value: Value<'v>,
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        self.get_ref_mut(heap)?.set_attr(attribute, alloc_value)
    }

    pub fn to_repr(self) -> String {
        let mut s = String::new();
        self.collect_repr(&mut s);
        s
    }

    pub fn new_invoker(self, heap: &'v Heap) -> anyhow::Result<FunctionInvoker<'v, '_>> {
        self.get_aref().new_invoker(self, heap)
    }

    pub fn set_at(
        self,
        index: Value<'v>,
        alloc_value: Value<'v>,
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        self.get_ref_mut(heap)?.set_at(index, alloc_value)
    }

    pub fn iterate(self, heap: &'v Heap) -> anyhow::Result<RefIterable<'v>> {
        let me: ARef<'v, dyn TypedValue> = self.get_aref();
        me.iterate()?;
        Ok(RefIterable::new(
            heap,
            ARef::map(me, |e| e.iterate().unwrap()),
        ))
    }

    pub fn get_type_value(self) -> &'static ConstFrozenValue {
        self.get_aref().get_type_value()
    }

    pub fn get_member(self, name: &str) -> Option<Value<'v>> {
        if let Some(members) = self.get_aref().get_members() {
            members.get(name)
        } else {
            None
        }
    }

    pub fn add_assign(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let aref = self.get_aref();
        if aref.naturally_mutable() {
            let upd = aref.add_assign(self, other)?;
            mem::drop(aref);
            // Important we have dropped the aref, since the function might want it mutably
            upd(heap)?;
            return Ok(self);
        } else {
            aref.add(self, other, heap)
        }
    }

    pub fn get_hashed(self) -> anyhow::Result<Hashed<Self>> {
        ValueLike::get_hashed(self)
    }

    pub fn downcast_ref<T: AnyLifetime<'v>>(self) -> Option<ARef<'v, T>> {
        ValueLike::downcast_ref(self)
    }

    pub fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        ValueLike::equals(self, other)
    }

    pub fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        ValueLike::compare(self, other)
    }

    /// Get a mutable reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function returns an `Err` if the `Value` is already borrowed, is frozen,
    /// or frozen for iteration.
    ///
    /// While this reference is active, any `get_aref` or similar on the value will
    /// _cause a panic_. Therefore, it's super important not to call any Starlark operations,
    /// even as simple as equality, while holding the `RefMut`.
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
    /// move on to `TypedValue` and include data from members.
    pub fn describe(self, name: &str) -> String {
        if self.get_aref().is_function() {
            format!("def {}: pass", self.to_repr().replace(" = ...", " = None"))
        } else {
            format!("# {} = {}", name, self.to_repr())
        }
    }
}
