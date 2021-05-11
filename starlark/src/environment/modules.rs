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
        Freezer, FrozenHeap, FrozenHeapRef, FrozenValue, Heap, OwnedFrozenValue, SimpleValue,
        StarlarkValue, Value, ValueLike,
    },
};
use gazebo::{any::AnyLifetime, prelude::*};
use itertools::Itertools;
use std::{mem, sync::Arc};

/// The result of freezing a [`Module`], making it and its contained values immutable.
///
/// The values of this [`FrozenModule`] are stored on a frozen heap, a reference to which
/// can be obtained using [`frozen_heap`](FrozenModule::frozen_heap). Be careful not to use
/// these values after the [`FrozenModule`] has been released unless you obtain a reference
/// to the frozen heap.
#[derive(Debug, Clone, Dupe)]
// We store the two elements separately since the FrozenHeapRef contains
// a copy of the FrozenModuleData inside it.
// Two Arc's should still be plenty cheap enough to qualify for `Dupe`.
pub struct FrozenModule(FrozenHeapRef, FrozenModuleRef);

#[derive(Debug, Clone, Dupe, AnyLifetime)]
pub(crate) struct FrozenModuleRef(pub(crate) Arc<FrozenModuleData>);

#[derive(Debug)]
pub(crate) struct FrozenModuleData {
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

/// A container for user values, used during execution.
///
/// A module contains both a [`FrozenHeap`] and [`Heap`] on which different values are allocated.
/// You can get references to these heaps with [`frozen_heap`](Module::frozen_heap) and
/// [`heap`](Module::heap). Be careful not to use these values after the [`Module`] has been
/// released unless you obtain a reference to the frozen heap.
#[derive(Debug)]
pub struct Module {
    heap: Heap,
    frozen_heap: FrozenHeap,
    names: MutableNames,
    // Should really be MutableSlots<'v>, where &'v self
    // Values are allocated from heap. Because of variance
    // you can inject the wrong values in, so make sure slots aren't
    // exported.
    slots: MutableSlots<'static>,
}

impl FrozenModule {
    /// Get the value of the variable `name`.
    /// Returns [`None`] if the variable isn't defined in the module or hasn't been set.
    pub fn get(&self, name: &str) -> Option<OwnedFrozenValue> {
        let slot = self.1.0.names.get_name(name)?;
        // This code is safe because we know the frozen module ref keeps the values alive
        self.1
            .0
            .slots
            .get_slot(slot)
            .map(|x| unsafe { OwnedFrozenValue::new(self.0.dupe(), x) })
    }

    /// Iterate through all the names defined in this module.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.1.names()
    }

    /// Obtain the [`FrozenHeapRef`] which owns the storage of all values defined in this module.
    pub fn frozen_heap(&self) -> &FrozenHeapRef {
        &self.0
    }

    /// Print out some approximation of the module definitions.
    pub fn describe(&self) -> String {
        self.1.describe()
    }
}

impl FrozenModuleRef {
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

    /// Try and go back from a slot to a name.
    /// Inefficient - only use in error paths.
    pub(crate) fn get_slot_name(&self, slot: usize) -> Option<String> {
        for (s, i) in self.0.names.symbols() {
            if *i == slot {
                return Some(s.clone());
            }
        }
        None
    }
}

impl<'v> StarlarkValue<'v> for FrozenModuleRef {
    starlark_type!("frozen_module");
}

impl SimpleValue for FrozenModuleRef {}

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

impl Default for Module {
    fn default() -> Self {
        Self::new()
    }
}

impl Module {
    /// Create a new module environment with no contents.
    pub fn new() -> Self {
        Self {
            heap: Heap::new(),
            frozen_heap: FrozenHeap::new(),
            names: MutableNames::new(),
            slots: MutableSlots::new(),
        }
    }

    /// Get the heap on which values are allocated by this module.
    pub fn heap(&self) -> &Heap {
        &self.heap
    }

    /// Get the frozen heap on which frozen values are allocated by this module.
    pub fn frozen_heap(&self) -> &FrozenHeap {
        &self.frozen_heap
    }

    pub(crate) fn names(&self) -> &MutableNames {
        &self.names
    }

    pub(crate) fn slots<'v>(&'v self) -> &'v MutableSlots<'v> {
        // Not true because of variance, but mostly true. Don't export further.
        unsafe { transmute!(&'v MutableSlots<'static>, &'v MutableSlots<'v>, &self.slots) }
    }

    /// Get the value of the variable `name`, or [`None`] if the variable is not defined.
    pub fn get<'v>(&'v self, name: &str) -> Option<Value<'v>> {
        let slot = self.names.get_name(name)?;
        self.slots().get_slot(slot)
    }

    /// Freeze the environment, all its value will become immutable afterwards.
    pub fn freeze(self) -> FrozenModule {
        let Module {
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
            names: names.freeze(),
            slots,
        }));
        FrozenModuleValue::set(&freezer, &rest);
        // The values MUST be alive up until this point (as the above line uses them),
        // but can now be dropped
        mem::drop(heap);

        FrozenModule(freezer.into_ref(), rest)
    }

    /// Set the value of a variable in the environment.
    /// Modifying these variables while executing is ongoing can have
    /// surprising effects.
    pub fn set<'v>(&'v self, name: &str, value: Value<'v>) {
        let slot = self.names.add_name(name);
        let slots = self.slots();
        slots.ensure_slots(slot + 1);
        slots.set_slot(slot, value);
    }

    fn is_public_symbol(symbol: &str) -> bool {
        !symbol.starts_with('_')
    }

    /// Import symbols from a module, similar to what is done during `load()`.
    pub fn import_public_symbols(&self, module: &FrozenModule) {
        self.frozen_heap.add_reference(&module.0);
        for (k, slot) in module.1.0.names.symbols() {
            if Self::is_public_symbol(k) {
                if let Some(value) = module.1.0.slots.get_slot(*slot) {
                    self.set(k, Value::new_frozen(value))
                }
            }
        }
    }

    pub(crate) fn load_symbol<'v>(
        &'v self,
        module: &FrozenModule,
        symbol: &str,
    ) -> anyhow::Result<Value<'v>> {
        if !Self::is_public_symbol(symbol) {
            return Err(EnvironmentError::CannotImportPrivateSymbol(symbol.to_owned()).into());
        }
        match module.get(symbol) {
            None => Err(EnvironmentError::VariableNotFound(symbol.to_owned()).into()),
            Some(v) => Ok(v.owned_value(self.frozen_heap())),
        }
    }
}

#[test]
fn test_send_sync()
where
    FrozenModule: Send + Sync,
{
}
