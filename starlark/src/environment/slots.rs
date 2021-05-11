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

use crate::values::{Freezer, FrozenValue, Heap, Value, ValueRef, Walker};
use gazebo::prelude::*;
use std::cell::{RefCell, RefMut};

#[derive(Clone, Copy, Dupe, Debug, PartialEq, Eq)]
pub(crate) struct LocalSlotId(usize);

impl LocalSlotId {
    pub fn new(index: usize) -> Self {
        Self(index)
    }
}

#[derive(Clone, Copy, Dupe, Debug, PartialEq, Eq)]
pub(crate) struct ModuleSlotId(usize);

impl ModuleSlotId {
    pub fn new(index: usize) -> Self {
        Self(index)
    }
}

/// Slots that are used in a local context, e.g. for a function that is executing.
/// Always mutable, never frozen. Uses the `ValueRef` because they have reference
/// semantics - if a variable gets mutated, someone who has a copy will see the
/// mutation.
#[derive(Default)]
pub(crate) struct LocalSlots<'v>(Vec<ValueRef<'v>>);

// Indexed slots of a module. May contain unassigned values
#[derive(Debug)]
pub(crate) struct MutableSlots<'v>(RefCell<Vec<Value<'v>>>);

// Indexed slots of a module. May contain unassigned values
#[derive(Debug)]
pub(crate) struct FrozenSlots(Vec<FrozenValue>);

impl<'v> MutableSlots<'v> {
    pub fn new() -> Self {
        Self(RefCell::new(Vec::new()))
    }

    pub(crate) fn get_slots_mut(&self) -> RefMut<Vec<Value<'v>>> {
        self.0.borrow_mut()
    }

    pub fn get_slot(&self, slot: ModuleSlotId) -> Option<Value<'v>> {
        let v = self.0.borrow()[slot.0];
        if v.is_unassigned() { None } else { Some(v) }
    }

    pub fn set_slot(&self, slot: ModuleSlotId, value: Value<'v>) {
        assert!(!value.is_unassigned());
        self.0.borrow_mut()[slot.0] = value;
    }

    pub fn ensure_slot(&self, slot: ModuleSlotId) {
        // To ensure that `slot` exists, we need at least `slot + 1` slots.
        self.ensure_slots(slot.0 + 1);
    }

    pub fn ensure_slots(&self, count: usize) {
        let mut slots = self.0.borrow_mut();
        if slots.len() >= count {
            return;
        }
        let extra = count - slots.len();
        slots.reserve(extra);
        for _ in 0..extra {
            slots.push(Value::new_unassigned());
        }
    }

    pub(crate) fn freeze(self, freezer: &Freezer) -> FrozenSlots {
        let slots = self.0.into_inner().map(|x| x.freeze(freezer));
        FrozenSlots(slots)
    }
}

impl FrozenSlots {
    pub fn get_slot(&self, slot: ModuleSlotId) -> Option<FrozenValue> {
        let fv = self.0[slot.0];
        if fv.is_unassigned() { None } else { Some(fv) }
    }
}

impl<'v> LocalSlots<'v> {
    pub fn new(values: Vec<ValueRef<'v>>) -> Self {
        Self(values)
    }

    /// Gets a local variable. Returns None to indicate the variable is not yet assigned.
    pub fn get_slot(&self, slot: LocalSlotId) -> Option<Value<'v>> {
        self.0[slot.0].get()
    }

    pub fn set_slot(&self, slot: LocalSlotId, value: Value<'v>) {
        self.0[slot.0].set(value);
    }

    /// Make a copy of this slot that can be used with `set_slot_ref` to
    /// bind two instances together.
    pub fn clone_slot_reference(&self, slot: LocalSlotId, heap: &'v Heap) -> ValueRef<'v> {
        self.0[slot.0].clone_reference(heap)
    }

    pub fn set_slot_ref(&mut self, slot: LocalSlotId, value_ref: ValueRef<'v>) {
        self.0[slot.0] = value_ref;
    }

    pub(crate) fn walk(&mut self, walker: &Walker<'v>) {
        self.0.iter_mut().for_each(|x| walker.walk_ref(x))
    }
}
