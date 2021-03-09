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

//! The environment, called "Module" in [this spec](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
//! is the list of variable in the current scope. It can be frozen, after which
//! all values from this environment become immutable.

use crate::{
    environment::{
        names::{FrozenNames, MutableNames},
        slots::{FrozenSlots, MutableSlots},
        EnvironmentError,
    },
    values::{
        Freezer, FrozenHeap, FrozenHeapRef, FrozenValue, Heap, ImmutableValue, OwnedFrozenValue,
        TypedValue, Value, ValueLike,
    },
};
use gazebo::{any::AnyLifetime, prelude::*};
use itertools::Itertools;
use std::{mem, sync::Arc};

// We store the two elements separately since the FrozenHeapRef contains
// a copy of the FrozenModuleData inside it.
// Two Arc's should still be plenty cheap enough to qualify for `Dupe`.
#[derive(Debug, Clone, Dupe)]
pub struct FrozenModule(FrozenHeapRef, FrozenModuleRef);

#[derive(Debug, Clone, Dupe, AnyLifetime)]
pub(crate) struct FrozenModuleRef(pub(crate) Arc<FrozenModuleData>);

#[derive(Debug)]
pub(crate) struct FrozenModuleData {
    name: String,
    pub(crate) names: FrozenNames,
    pub(crate) slots: FrozenSlots,
}

// When a definition is frozen, it still needs to get at some module info,
// specifically the slots (for execution) and the names (for debugging).
// Since the module slots also reference the definitions, they can't use a
// normal Arc since otherwise we'll have a loop and never collect a module.
// Solution is to put the slots in the heap, as a `FrozenValue`, then
// we wrap a `FrozenModuleValue` around it to give some type safety and a place
// to put the APIs.
#[derive(Clone, Dupe, Copy)]
// Deliberately don't derive Debug, since this value often occurs in cycles,
// and Debug printing of that would be bad.
pub(crate) struct FrozenModuleValue(FrozenValue); // Must contain a FrozenModuleRef inside it

#[derive(Debug)]
pub struct Module {
    heap: Heap,
    frozen_heap: FrozenHeap,
    name: String,
    names: MutableNames,
    // Should really be MutableSlots<'v>, where &'v self
    // Values are allocated from heap. Because of variance
    // you can inject the wrong values in, so make sure slots aren't
    // exported.
    slots: MutableSlots<'static>,
}

impl FrozenModule {
    /// Get the value of the variable `name`.
    /// Returns None if the variable isn't in the module or hasn't been set.
    pub fn get(&self, name: &str) -> Option<OwnedFrozenValue> {
        let slot = self.1.0.names.get_name(name)?;
        self.1
            .0
            .slots
            .get_slot(slot)
            .map(|x| OwnedFrozenValue::new(self.0.dupe(), x))
    }

    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.1.names()
    }

    pub fn frozen_heap(&self) -> &FrozenHeapRef {
        &self.0
    }

    pub fn describe(&self) -> String {
        self.1.describe()
    }
}

impl FrozenModuleRef {
    pub fn name(&self) -> &str {
        &self.0.name
    }

    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.0.names.symbols().map(|x| x.0.as_str())
    }

    pub fn describe(&self) -> String {
        self.0
            .names
            .symbols()
            .filter_map(|(name, slot)| Some((name, self.0.slots.get_slot(*slot)?)))
            .map(|(name, val)| val.to_value().describe(name))
            .join("\n")
    }

    pub(crate) fn get_slot(&self, slot: usize) -> Option<FrozenValue> {
        self.0.slots.get_slot(slot)
    }
}

impl<'v> TypedValue<'v> for FrozenModuleRef {
    starlark_type!("frozen_module");
}

impl<'v> ImmutableValue<'v> for FrozenModuleRef {}

impl FrozenModuleValue {
    pub fn new(freezer: &Freezer) -> Self {
        Self(freezer.get_magic())
    }

    pub fn set(freezer: &Freezer, val: &FrozenModuleRef) {
        freezer.set_magic(val.dupe())
    }

    pub fn get(self) -> FrozenModuleRef {
        self.0.downcast_ref::<FrozenModuleRef>().unwrap().dupe()
    }
}

impl Module {
    /// Create a new module environment
    pub fn new(name: &str) -> Self {
        Self {
            heap: Heap::new(),
            frozen_heap: FrozenHeap::new(),
            name: name.to_owned(),
            names: MutableNames::new(),
            slots: MutableSlots::new(),
        }
    }

    pub fn heap(&self) -> &Heap {
        &self.heap
    }

    pub fn frozen_heap(&self) -> &FrozenHeap {
        &self.frozen_heap
    }

    /// Return the name of this module
    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn names(&self) -> &MutableNames {
        &self.names
    }

    pub(crate) fn slots<'v>(&'v self) -> &'v MutableSlots<'v> {
        // Not true because of variance, but mostly true. Don't export further.
        unsafe { transmute!(&'v MutableSlots<'static>, &'v MutableSlots<'v>, &self.slots) }
    }

    /// Get the value of the variable `name`
    pub fn get<'v>(&'v self, name: &str) -> Option<Value<'v>> {
        let slot = self.names.get_name(name)?;
        self.slots().get_slot(slot)
    }

    /// Freeze the environment, all its value will become immutable after that
    pub fn freeze(self) -> FrozenModule {
        let Module {
            name,
            names,
            slots,
            frozen_heap,
            heap,
        } = self;
        // This is when we do the GC/freeze, using the module slots as roots
        // Note that we even freeze anonymous slots, since they are accessed by
        // slot-index in the code, and we don't walk into them, so don't know if
        // they are used.
        let freezer = Freezer::new(frozen_heap);
        let slots = slots.freeze(&freezer);
        let rest = FrozenModuleRef(Arc::new(FrozenModuleData {
            name,
            names: names.freeze(),
            slots,
        }));
        FrozenModuleValue::set(&freezer, &rest);
        // The values MUST be alive up until this point (as the above line uses them),
        // but can now be dropped
        mem::drop(heap);

        FrozenModule(freezer.into_ref(), rest)
    }

    /// Set the value of a variable in that environment.
    pub fn set<'v>(&'v self, name: &str, value: Value<'v>) {
        // Doesn't technically require &mut, but does morally
        let slot = self.names.add_name(name);
        let slots = self.slots();
        slots.ensure_slots(slot + 1);
        slots.set_slot(slot, value);
    }

    fn is_public_symbol(symbol: &str) -> bool {
        !symbol.starts_with('_')
    }

    pub fn import_public_symbols(&self, env: &FrozenModule) {
        self.frozen_heap.add_reference(&env.0);
        for (k, slot) in env.1.0.names.symbols() {
            if Self::is_public_symbol(k) {
                if let Some(value) = env.1.0.slots.get_slot(*slot) {
                    self.set(k, Value::new_frozen(value))
                }
            }
        }
    }

    pub(crate) fn load_symbol<'v>(
        &'v self,
        env: &FrozenModule,
        symbol: &str,
    ) -> anyhow::Result<Value<'v>> {
        if !Self::is_public_symbol(symbol) {
            return Err(EnvironmentError::CannotImportPrivateSymbol(symbol.to_owned()).into());
        }
        match env.get(symbol) {
            None => Err(EnvironmentError::VariableNotFound(symbol.to_owned()).into()),
            Some(v) => Ok(v.owned_value(self)),
        }
    }
}

#[test]
fn test_send_sync()
where
    FrozenModule: Send + Sync,
{
}
