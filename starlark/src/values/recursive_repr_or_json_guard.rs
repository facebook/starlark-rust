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

//! Detect recursion when doing `repr` or `to_json`.

use std::{cell::Cell, intrinsics::unlikely};

use crate::{collections::SmallSet, values::Value};

/// Pop the stack on drop.
pub(crate) struct ReprStackGuard;

/// Pop the stack on drop.
pub(crate) struct JsonStackGuard;

impl Drop for ReprStackGuard {
    fn drop(&mut self) {
        let mut stack = REPR_STACK.take();
        let popped = stack.pop();
        debug_assert!(popped.is_some());
        REPR_STACK.set(stack);
    }
}

impl Drop for JsonStackGuard {
    fn drop(&mut self) {
        let mut stack = JSON_STACK.take();
        let popped = stack.pop();
        debug_assert!(popped.is_some());
        JSON_STACK.set(stack);
    }
}

/// Returned when `repr` is called recursively and a cycle is detected.
pub(crate) struct ReprCycle;

/// Returned when `to_json` is called recursively and a cycle is detected.
pub(crate) struct JsonCycle;

#[thread_local]
static REPR_STACK: Cell<SmallSet<usize>> = Cell::new(SmallSet::new());

#[thread_local]
static JSON_STACK: Cell<SmallSet<usize>> = Cell::new(SmallSet::new());

/// Push a value to the stack, return error if it is already on the stack.
pub(crate) fn repr_stack_push(value: Value) -> Result<ReprStackGuard, ReprCycle> {
    let mut stack = REPR_STACK.take();
    if unlikely(!stack.insert(value.ptr_value())) {
        REPR_STACK.set(stack);
        Err(ReprCycle)
    } else {
        REPR_STACK.set(stack);
        Ok(ReprStackGuard)
    }
}

/// Push a value to the stack, return error if it is already on the stack.
pub(crate) fn json_stack_push(value: Value) -> Result<JsonStackGuard, JsonCycle> {
    let mut stack = JSON_STACK.take();
    if unlikely(!stack.insert(value.ptr_value())) {
        JSON_STACK.set(stack);
        Err(JsonCycle)
    } else {
        JSON_STACK.set(stack);
        Ok(JsonStackGuard)
    }
}

/// Release excessive memory allocated for the stack.
/// This is needed to make leak sanitizer happy.
fn repr_stack_release_memory() {
    let stack = REPR_STACK.take();
    if !stack.is_empty() {
        REPR_STACK.set(stack);
    }
}

/// Release excessive memory allocated for the stack.
/// This is needed to make leak sanitizer happy.
fn json_stack_release_memory() {
    let stack = JSON_STACK.take();
    if !stack.is_empty() {
        JSON_STACK.set(stack);
    }
}

/// Release excessive memory allocated for the stack on drop.
pub(crate) struct ReprStackReleaseMemoryOnDrop;

/// Release excessive memory allocated for the stack on drop.
pub(crate) struct JsonStackReleaseMemoryOnDrop;

impl Drop for ReprStackReleaseMemoryOnDrop {
    fn drop(&mut self) {
        repr_stack_release_memory();
    }
}

impl Drop for JsonStackReleaseMemoryOnDrop {
    fn drop(&mut self) {
        json_stack_release_memory();
    }
}
