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

use crate::{
    environment::{names::MutableNames, slots::ModuleSlotId},
    eval::runtime::slots::LocalSlotId,
    syntax::ast::{AstAssign, AstStmt, Expr, Stmt},
};
use std::collections::{hash_map, HashMap};

pub(crate) struct Scope<'a> {
    module: &'a MutableNames,
    // The first locals is the anon-slots for load() and comprehensions at the module-level
    // The rest are anon-slots for functions (which include their comprehensions)
    locals: Vec<ScopeNames>,
    unscopes: Vec<Unscope>,
}

struct UnscopeBinding {
    slot: LocalSlotId,
    /// Variable mappings in local scope are overwritten by comprehension variables.
    ///
    /// When we enter comprehension, we replace local scope variable slots with comprehension
    /// scope slots. This field stores the original slot in the local scope,
    /// or `None` if there was no mapping for the variable.
    ///
    /// When we pop the comprehension scope, we restore the mapping from this value.
    undo: Option<LocalSlotId>,
}

#[derive(Default)]
struct Unscope(HashMap<String, UnscopeBinding>);

#[derive(Default, Debug)]
pub(crate) struct ScopeNames {
    /// The number of slots this scope uses, including for parameters and `parent`.
    /// The next required slot would be at index `used`.
    pub used: usize,
    /// The names that are in this scope
    pub mp: HashMap<String, LocalSlotId>,
    /// Slots to copy from the parent. (index in parent, index in child).
    /// Module-level identifiers are not copied over, to avoid excess copying.
    pub parent: Vec<(LocalSlotId, LocalSlotId)>,
}

impl ScopeNames {
    fn copy_parent(&mut self, parent: LocalSlotId, name: &str) -> LocalSlotId {
        assert!(self.get_name(name).is_none()); // Or we'll be overwriting our variable
        let res = self.add_name(name);
        self.parent.push((parent, res));
        res
    }

    fn next_slot(&mut self) -> LocalSlotId {
        let res = LocalSlotId::new(self.used);
        self.used += 1;
        res
    }

    fn add_name(&mut self, name: &str) -> LocalSlotId {
        match self.mp.get(name) {
            Some(v) => *v,
            None => {
                let slot = self.next_slot();
                self.mp.insert(name.to_owned(), slot);
                slot
            }
        }
    }

    fn add_scoped(&mut self, name: &str, unscope: &mut Unscope) -> LocalSlotId {
        match unscope.0.entry(name.to_owned()) {
            hash_map::Entry::Occupied(e) => e.get().slot,
            hash_map::Entry::Vacant(e) => {
                let slot = self.next_slot();
                let undo = match self.mp.get_mut(name) {
                    Some(v) => {
                        let old = *v;
                        *v = slot;
                        Some(old)
                    }
                    None => {
                        self.mp.insert(name.to_owned(), slot);
                        None
                    }
                };
                e.insert(UnscopeBinding { slot, undo });
                slot
            }
        }
    }

    fn unscope(&mut self, unscope: Unscope) {
        for (name, UnscopeBinding { undo, .. }) in unscope.0 {
            match undo {
                None => {
                    self.mp.remove(&name);
                }
                Some(v) => *self.mp.get_mut(&name).unwrap() = v,
            }
        }
    }

    fn get_name(&self, name: &str) -> Option<LocalSlotId> {
        self.mp.get(name).copied()
    }
}

pub(crate) enum Slot {
    Module(ModuleSlotId), // Top-level module scope
    Local(LocalSlotId),   // Local scope, always mutable
}

impl<'a> Scope<'a> {
    pub fn enter_module(module: &'a MutableNames, code: &AstStmt) -> Self {
        let mut locals = HashMap::new();
        Stmt::collect_defines(code, &mut locals);
        for (x, vis) in locals {
            module.add_name_visibility(x, vis);
        }
        Self {
            module,
            locals: vec![ScopeNames::default()],
            unscopes: Vec::new(),
        }
    }

    // Number of module slots I need, number of local anon slots I need
    pub fn exit_module(mut self) -> (usize, usize) {
        assert!(self.locals.len() == 1);
        assert!(self.unscopes.is_empty());
        let scope = self.locals.pop().unwrap();
        assert!(scope.parent.is_empty());
        (self.module.slot_count(), scope.used)
    }

    pub fn enter_def<'s>(&mut self, params: impl Iterator<Item = &'s str>, code: &AstStmt) {
        let mut names = ScopeNames::default();
        for p in params {
            // Subtle invariant: the slots for the params must be ordered and at the
            // beginning
            names.add_name(p);
        }
        let mut locals = HashMap::new();
        Stmt::collect_defines(code, &mut locals);
        // Note: this process introduces non-determinism, as the defines are collected in different orders each time
        for x in locals.into_iter() {
            names.add_name(x.0);
        }
        self.locals.push(names);
    }

    // Which slots to grab from the current scope to the parent scope, size of your
    // self scope Future state: Should return the slots to use from the parent
    // scope
    pub fn exit_def(&mut self) -> ScopeNames {
        self.locals.pop().unwrap()
    }

    pub fn enter_compr(&mut self) {
        self.unscopes.push(Unscope::default());
    }

    pub fn add_compr(&mut self, var: &AstAssign) {
        let mut locals = HashMap::new();
        Expr::collect_defines_lvalue(var, &mut locals);
        for k in locals.into_iter() {
            self.locals
                .last_mut()
                .unwrap()
                .add_scoped(k.0, self.unscopes.last_mut().unwrap());
        }
    }

    pub fn exit_compr(&mut self) {
        self.locals
            .last_mut()
            .unwrap()
            .unscope(self.unscopes.pop().unwrap());
    }

    pub fn get_name(&mut self, name: &str) -> Option<Slot> {
        // look upwards to find the first place the variable occurs
        // then copy that variable downwards
        for i in (0..self.locals.len()).rev() {
            if let Some(mut v) = self.locals[i].get_name(name) {
                for j in (i + 1)..self.locals.len() {
                    v = self.locals[j].copy_parent(v, name);
                }
                return Some(Slot::Local(v));
            }
        }
        self.module
            .get_name(name)
            .map(|(slot, _vis)| Slot::Module(slot))
    }

    pub fn get_name_or_panic(&mut self, name: &str) -> Slot {
        self.get_name(name).unwrap_or_else(|| {
            panic!(
                "Scope::get_name, internal error, entry missing from scope table `{}`",
                name
            )
        })
    }
}
