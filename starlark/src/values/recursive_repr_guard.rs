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

//! Detect recursion when doing `repr`.

use std::{cell::Cell, intrinsics::unlikely};

use crate::{collections::SmallSet, values::Value};

/// Pop the stack on drop.
pub(crate) struct ReprStackGuard;

impl Drop for ReprStackGuard {
    fn drop(&mut self) {
        let mut stack = STACK.take();
        let popped = stack.pop();
        debug_assert!(popped.is_some());
        STACK.set(stack);
    }
}

/// Returned when `repr` is called recursively and a cycle is detected.
pub(crate) struct ReprCycle;

#[thread_local]
static STACK: Cell<SmallSet<usize>> = Cell::new(SmallSet::new());

/// Push a value to the stack, return error if it is already on the stack.
pub(crate) fn repr_stack_push(value: Value) -> Result<ReprStackGuard, ReprCycle> {
    let mut stack = STACK.take();
    if unlikely(!stack.insert(value.ptr_value())) {
        STACK.set(stack);
        Err(ReprCycle)
    } else {
        STACK.set(stack);
        Ok(ReprStackGuard)
    }
}

/// Release excessive memory allocated for the stack.
/// This is needed to make leak sanitizer happy.
fn repr_stack_release_memory() {
    let stack = STACK.take();
    if !stack.is_empty() {
        STACK.set(stack);
    }
}

/// Release excessive memory allocated for the stack on drop.
pub(crate) struct ReprStackReleaseMemoryOnDrop;

impl Drop for ReprStackReleaseMemoryOnDrop {
    fn drop(&mut self) {
        repr_stack_release_memory();
    }
}
