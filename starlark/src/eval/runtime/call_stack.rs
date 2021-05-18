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
    codemap::FileSpan,
    errors::Frame,
    values::{ControlError, Value, Walker},
};
use gazebo::prelude::*;
use std::{fmt, fmt::Debug};

// A value akin to Frame, but can be created cheaply, since it doesn't resolve
// anything in advance.
// The downside is it has a lifetime on 'v and keeps alive the whole CodeMap.
struct CheapFrame<'v> {
    function: Value<'v>,
    location: Option<FileSpan>,
}

impl CheapFrame<'_> {
    fn to_frame(&self) -> Frame {
        Frame {
            name: self.function.to_repr(),
            location: self.location.dupe(),
        }
    }
}

impl Debug for CheapFrame<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut x = f.debug_struct("Frame");
        x.field("function", &self.function);
        x.field("location", &self.location);
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
        location: Option<FileSpan>,
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
    pub fn top_location(&self) -> Option<FileSpan> {
        self.stack.last()?.location.dupe()
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
