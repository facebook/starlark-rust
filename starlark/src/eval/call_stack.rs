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

//! Starlark call stack.

// FIXME: I think we should rewrite the CallStack stuff entirely:
// * Don't keep a call stack, just a call stack depth.
// * When people did StackGuard.inc just do CallStack.inc, we need less info
// once it's an int so can reuse.
// * When an exception happens, decorate it with the call stack on the way back
//   up, in eval_call.

use crate::{
    codemap::{CodeMap, Span, SpanLoc},
    errors::Frame,
    values::{ControlError, Value, Walker},
};
use std::{cell::Cell, fmt, fmt::Debug, sync::Arc};

// A value akin to Frame, but can be created cheaply, since it doesn't resolve
// anything in advance.
// The downside is it has a lifetime on 'v and keeps alive the whole CodeMap.
struct CheapFrame<'v> {
    function: Value<'v>,
    location: Option<(Arc<CodeMap>, Span)>,
}

impl CheapFrame<'_> {
    fn resolve_location(&self) -> Option<SpanLoc> {
        self.location
            .as_ref()
            .map(|(codemap, span)| codemap.look_up_span(*span))
    }

    fn to_frame(&self) -> Frame {
        Frame {
            name: self.function.to_repr(),
            location: self.resolve_location(),
        }
    }
}

impl Debug for CheapFrame<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut x = f.debug_struct("Frame");
        x.field("function", &self.function);
        x.field("location", &self.resolve_location());
        x.finish()
    }
}

/// Starlark call stack.
#[derive(Debug, Default)]
pub(crate) struct CallStack<'v> {
    stack: Vec<CheapFrame<'v>>,
}

// At 50 we see the C stack overflowing, so limit to 40 (which seems quite
// low...)
const MAX_CALLSTACK_RECURSION: usize = 40;

impl<'v> CallStack<'v> {
    /// Push an element to the stack. It is important the each `push` is paired
    /// with a `pop`.
    pub(crate) fn push(
        &mut self,
        function: Value<'v>,
        location: Option<(Arc<CodeMap>, Span)>,
    ) -> anyhow::Result<()> {
        if self.stack.len() > MAX_CALLSTACK_RECURSION {
            return Err(ControlError::TooManyRecursionLevel.into());
        }
        self.stack.push(CheapFrame { function, location });
        Ok(())
    }

    /// Remove the top element from the stack. Called after `push`.
    pub(crate) fn pop(&mut self) {
        let old = self.stack.pop();
        assert!(
            old.is_some(),
            "CallStack.pop() called without preceding push()"
        )
    }

    /// The location at the top of the stack. May be `None` if
    /// either there the stack is empty, or the top of the stack lacks location
    /// information (e.g. called from Rust).
    pub fn top_location(&self) -> Option<SpanLoc> {
        self.stack.last()?.resolve_location()
    }

    pub(crate) fn walk(&mut self, walker: &Walker<'v>) {
        for x in self.stack.iter_mut() {
            walker.walk(&mut x.function);
        }
    }

    pub fn to_diagnostic_frames(&self) -> Vec<Frame> {
        // The first entry is just the entire module, so skip it
        self.stack
            .iter()
            .skip(1)
            .map(CheapFrame::to_frame)
            .collect()
    }

    /// List the entries on the stack as values
    pub(crate) fn to_function_values(&self) -> Vec<Value<'v>> {
        self.stack.iter().skip(1).map(|x| x.function).collect()
    }
}

// Maximum recursion level for comparison
// TODO(dmarting): those are rather short, maybe make it configurable?
#[cfg(debug_assertions)]
const MAX_RECURSION: u32 = 200;

#[cfg(not(debug_assertions))]
const MAX_RECURSION: u32 = 3000;

// A thread-local counter is used to detect too deep recursion.
//
// Thread-local is chosen instead of explicit function "recursion" parameter
// for two reasons:
// * It's possible to propagate stack depth across external functions like
//   `Display::to_string` where passing a stack depth parameter is hard
// * We need to guarantee that stack depth is not lost in complex invocation
//   chains like function calls compare which calls native function which calls
//   starlark function which calls to_str. We could change all evaluation stack
//   signatures to accept some "context" parameters, but passing it as
//   thread-local is easier.
thread_local!(static STACK_DEPTH: Cell<u32> = Cell::new(0));

/// Stored previous stack depth before calling `try_inc`.
///
/// Stores that previous stack depths back to thread-local on drop.
#[must_use]
// QUESTION: Is this useful? If we build a deep structure so deep equals
//           dies, won't we just die in `drop` anyway?
pub struct StackGuard {
    prev_depth: u32,
}

impl Drop for StackGuard {
    fn drop(&mut self) {
        STACK_DEPTH.with(|c| c.set(self.prev_depth));
    }
}

/// Increment stack depth.
fn inc() -> StackGuard {
    let prev_depth = STACK_DEPTH.with(|c| {
        let prev = c.get();
        c.set(prev + 1);
        prev
    });
    StackGuard { prev_depth }
}

/// Check stack depth does not exceed configured max stack depth.
fn check() -> anyhow::Result<()> {
    if STACK_DEPTH.with(Cell::get) >= MAX_RECURSION {
        return Err(ControlError::TooManyRecursionLevel.into());
    }
    Ok(())
}

/// Try increment stack depth.
///
/// Return opaque `StackGuard` object which resets stack to previous value
/// on `drop`.
///
/// If stack depth exceeds configured limit, return error.
pub fn try_inc() -> anyhow::Result<StackGuard> {
    check()?;
    Ok(inc())
}
