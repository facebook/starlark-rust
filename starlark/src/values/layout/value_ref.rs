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

use crate as starlark;
use crate::values::{
    layout::{
        heap::{Freezer, Heap},
        value::{FrozenValue, Value, ValueMem},
    },
    Trace,
};
use gazebo::{coerce::Coerce, prelude::*};
use std::cell::Cell;

/// A value that might have reference semantics.
/// References are required when a lambda captures an outer variable,
/// as all subsequent modifications of the outer variable will be
/// reflected in the inner.
/// However, most values captured are not by reference, so use the user_tag
/// to indicate whether a value is a `Ref` (and must be dereffed a lot),
/// or just a normal `Value` (much cheaper).
/// A normal `Value` cannot be `ValueMem::Ref`, but this one might be.
#[derive(Debug, Trace, Coerce, Clone, Dupe)]
#[repr(transparent)]
pub(crate) struct ValueRef<'v>(pub(crate) Cell<Option<Value<'v>>>);

impl<'v> ValueRef<'v> {
    // Get the cell, chasing down any forwarding if it exists.
    // We have the invariant that if we have a ref we always set the user tag
    fn get_cell(&self) -> &Cell<Option<Value<'v>>> {
        match self.0.get() {
            Some(v) if v.0.get_user_tag() => match v.0.unpack_ptr2() {
                Some(ValueMem::Ref(cell)) => cell,
                _ => unreachable!(),
            },
            _ => &self.0,
        }
    }

    pub fn new_unassigned() -> Self {
        Self(Cell::new(None))
    }

    pub fn new_frozen(x: Option<FrozenValue>) -> Self {
        Self(Cell::new(x.map(Value::new_frozen)))
    }

    pub fn set(&self, value: Value<'v>) {
        self.get_cell().set(Some(value));
    }

    fn is_ref(&self) -> bool {
        match self.0.get() {
            Some(v) => v.0.get_user_tag(),
            _ => false,
        }
    }

    // Only valid if there is no chance this is a real ref
    pub fn set_direct(&self, value: Value<'v>) {
        debug_assert!(!self.is_ref());
        self.0.set(Some(value));
    }

    // Only valid if there is no chance this is a real ref
    pub fn get_direct(&self) -> Option<Value<'v>> {
        debug_assert!(!self.is_ref());
        self.0.get()
    }

    pub fn get(&self) -> Option<Value<'v>> {
        self.get_cell().get()
    }

    /// Return a new `ValueRef` that points at the same underlying memory as the original.
    /// Updates to either will result in both changing.
    pub fn clone_reference(&self, heap: &'v Heap) -> ValueRef<'v> {
        match self.0.get() {
            Some(v) if v.0.get_user_tag() => match v.0.unpack_ptr2() {
                Some(ValueMem::Ref(_)) => Self(Cell::new(Some(v))),
                _ => panic!(),
            },
            v => {
                let reffed = Value(heap.alloc_raw(ValueMem::Ref(Cell::new(v))).0.set_user_tag());
                self.0.set(Some(reffed));
                Self(Cell::new(Some(reffed)))
            }
        }
    }

    /// Create a duplicate `ValueRef` on something that must have been turned into a real ref,
    /// probably via `clone_reference`.
    pub fn dupe_reference(&self) -> ValueRef<'v> {
        debug_assert!(self.0.get().unwrap().0.get_user_tag());
        Self(self.0.dupe())
    }

    pub fn freeze(&self, freezer: &Freezer) -> anyhow::Result<Option<FrozenValue>> {
        self.get_cell().get().into_try_map(|x| freezer.freeze(x))
    }
}
