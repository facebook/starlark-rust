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

use crate::{
    collections::SmallMap,
    stdlib::standard_environment,
    values::{
        structs::FrozenStruct, AllocFrozenValue, FrozenHeap, FrozenHeapRef, FrozenValue, Value,
    },
};
use gazebo::prelude::*;
use itertools::Itertools;
use once_cell::sync::OnceCell;
use std::{collections::HashMap, mem, sync::Arc};

#[derive(Clone, Dupe, Debug)]
pub struct Globals(Arc<GlobalsData>);

#[derive(Debug)]
struct GlobalsData {
    heap: FrozenHeapRef,
    variables: HashMap<String, FrozenValue>,
}

impl Default for Globals {
    fn default() -> Self {
        standard_environment().build()
    }
}

// Why are these things RefCell? Because we need to allocate things from the heap
// which returns values pointing at the heap, and thus are an immutable borrow.
// Once you have that, you can't mutably borrow at the same time, so have to use
// interior mutability.
#[derive(Debug)]
pub struct GlobalsBuilder {
    // The heap everything is allocated in
    heap: FrozenHeap,
    // Normal top-level variables, e.g. True/hash
    variables: HashMap<String, FrozenValue>,
    // Set to Some when we are in a struct builder, otherwise None
    struct_fields: Option<SmallMap<String, FrozenValue>>,
}

impl Globals {
    pub fn get<'v>(&self, name: &str) -> Option<Value<'v>> {
        self.get_frozen(name).map(FrozenValue::to_value)
    }

    pub(crate) fn get_frozen(&self, name: &str) -> Option<FrozenValue> {
        self.0.variables.get(name).copied()
    }

    pub fn names(&self) -> Vec<String> {
        self.0.variables.keys().cloned().collect()
    }

    pub fn heap(&self) -> &FrozenHeapRef {
        &self.0.heap
    }

    pub fn describe(&self) -> String {
        self.0
            .variables
            .iter()
            .map(|(name, val)| val.to_value().describe(name))
            .join("\n")
    }
}

impl GlobalsBuilder {
    pub fn new() -> Self {
        Self {
            heap: FrozenHeap::new(),
            variables: HashMap::new(),
            struct_fields: None,
        }
    }

    pub fn struct_(&mut self, name: &str, f: impl Fn(&mut GlobalsBuilder)) {
        assert!(
            self.struct_fields.is_none(),
            "Can't recursively nest GlobalsBuilder::struct_"
        );
        self.struct_fields = Some(SmallMap::new());
        f(self);
        let fields = mem::take(&mut self.struct_fields).unwrap();
        self.set(name, FrozenStruct { fields });
    }

    pub fn with(mut self, f: impl FnOnce(&mut Self)) -> Self {
        f(&mut self);
        self
    }

    pub fn with_struct(mut self, name: &str, f: impl Fn(&mut GlobalsBuilder)) -> Self {
        self.struct_(name, f);
        self
    }

    pub fn build(self) -> Globals {
        Globals(Arc::new(GlobalsData {
            heap: self.heap.into_ref(),
            variables: self.variables,
        }))
    }

    pub fn set<'v, V: AllocFrozenValue<'v>>(&'v mut self, name: &str, value: V) {
        let name = name.to_owned();
        let value = value.alloc_frozen_value(&self.heap);
        match &mut self.struct_fields {
            None => self.variables.insert(name, value),
            Some(fields) => fields.insert(name, value),
        };
    }

    pub fn alloc<'v, V: AllocFrozenValue<'v>>(&'v self, value: V) -> FrozenValue {
        value.alloc_frozen_value(&self.heap)
    }
}

/// Used to create some static members for a `StarlarkValue`, usually written as:
///
/// ```ignore
/// fn get_members(&self) -> Option<&'static Globals> {
///     static RES: GlobalsStatic = GlobalsStatic::new();
///     RES.members(module_creator)
/// }
/// ```
pub struct GlobalsStatic(OnceCell<Globals>);

impl GlobalsStatic {
    pub const fn new() -> Self {
        Self(OnceCell::new())
    }

    fn globals(&'static self, x: impl FnOnce(&mut GlobalsBuilder)) -> &'static Globals {
        self.0.get_or_init(|| GlobalsBuilder::new().with(x).build())
    }

    pub fn members(&'static self, x: impl FnOnce(&mut GlobalsBuilder)) -> Option<&'static Globals> {
        Some(self.globals(x))
    }

    /// Requires that the `#[starlark_module]` has a single function in it.
    pub fn function(&'static self, x: impl FnOnce(&mut GlobalsBuilder)) -> FrozenValue {
        let globals = self.globals(x);
        if globals.0.variables.len() != 1 {
            panic!(
                "GlobalsBuilder.function must have exactly 1 member, you had {:?}",
                globals.names()
            );
        }
        *globals.0.variables.values().next().unwrap()
    }
}

#[test]
fn test_send_sync()
where
    Globals: Send + Sync,
{
}
