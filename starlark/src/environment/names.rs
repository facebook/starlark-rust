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

use std::{cell::RefCell, collections::HashMap, iter::Iterator};

/// MutableNames are how we allocate slots (index-based) to variables
/// (name-based). The slots field is the current active mapping of names to
/// index.
///
/// In a statement context there are things that define variables, e.g. x=...,
/// for x in ... Importantly, the expression x can refer to either a global x,
/// or a local x that hasn't yet been defined, based on the future
/// presence/absence of a statement defining x. Therefore, we first capture all
/// the definitions with collect_defines_lvalue, allocate them slots,
/// then replace variables with slot numbers when compiling.
///
/// Comprehensions are a bit different. Given [x for x in y] that defines x, but
/// in a way that shadows any existing x, and the definition immediately binds
/// x. We do that with add_scoped()/unscope(). On an add_scope, we allocate
/// fresh slots at the end, and bind them to the names in the comprehension.
/// On an unscope, we do the reverse, putting things back to how they were
/// before (apart from the total) number of slots required.
#[derive(Debug)]
pub(crate) struct MutableNames(RefCell<HashMap<String, usize>>);

#[derive(Debug)]
pub(crate) struct FrozenNames(HashMap<String, usize>);

impl MutableNames {
    pub fn new() -> Self {
        Self(RefCell::new(HashMap::new()))
    }

    pub fn slot_count(&self) -> usize {
        self.0.borrow().len()
    }

    /// Try and go back from a slot to a name.
    /// Inefficient - only use in error paths.
    pub fn get_slot(&self, slot: usize) -> Option<String> {
        for (s, i) in &*self.0.borrow() {
            if *i == slot {
                return Some(s.clone());
            }
        }
        None
    }

    pub fn get_name(&self, name: &str) -> Option<usize> {
        self.0.borrow().get(name).copied()
    }

    // Add a name, or if it's already there, return the existing name
    pub fn add_name(&self, name: &str) -> usize {
        let mut x = self.0.borrow_mut();
        match x.get(name) {
            Some(v) => *v,
            None => {
                let slot = x.len();
                x.insert(name.to_owned(), slot);
                slot
            }
        }
    }

    pub fn hide_name(&self, name: &str) {
        self.0.borrow_mut().remove(name);
    }

    pub fn all_names(&self) -> HashMap<String, usize> {
        self.0.borrow().clone()
    }

    pub fn freeze(self) -> FrozenNames {
        FrozenNames(self.0.into_inner())
    }
}

impl FrozenNames {
    pub fn get_name(&self, name: &str) -> Option<usize> {
        self.0.get(name).copied()
    }

    pub fn symbols(&self) -> impl Iterator<Item = (&String, &usize)> {
        self.0.iter()
    }
}
