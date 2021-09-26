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
    codemap::{CodeMap, FileSpan, Span},
    errors::Frame,
    values::{ControlError, Trace, Tracer, Value},
};
use gazebo::prelude::*;
use std::{fmt, fmt::Debug, intrinsics::unlikely};

// A value akin to Frame, but can be created cheaply, since it doesn't resolve
// anything in advance.
// The downside is it has a lifetime on 'v and keeps alive the whole CodeMap.
#[derive(Clone, Copy, Dupe)]
struct CheapFrame<'v> {
    function: Value<'v>,
    file: Option<&'v CodeMap>,
    span: Span,
}

impl CheapFrame<'_> {
    fn location(&self) -> Option<FileSpan> {
        self.file.map(|file| FileSpan {
            file: file.dupe(),
            span: self.span,
        })
    }

    fn to_frame(&self) -> Frame {
        Frame {
            name: self.function.to_repr(),
            location: self.location(),
        }
    }
}

impl Debug for CheapFrame<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut x = f.debug_struct("Frame");
        x.field("function", &self.function);
        x.field("span", &self.span);
        x.field("file", &self.file);
        x.finish()
    }
}

/// Starlark call stack.
#[derive(Debug)]
pub(crate) struct CallStack<'v> {
    count: usize,
    stack: [CheapFrame<'v>; MAX_CALLSTACK_RECURSION],
}

impl<'v> Default for CallStack<'v> {
    fn default() -> Self {
        Self {
            count: 0,
            stack: [CheapFrame {
                function: Value::new_none(),
                file: None,
                span: Span::default(),
            }; MAX_CALLSTACK_RECURSION],
        }
    }
}

// At 50 we see the C stack overflowing, so limit to 40 (which seems quite
// low...)
const MAX_CALLSTACK_RECURSION: usize = 40;

unsafe impl<'v> Trace<'v> for CallStack<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        for x in self.stack[0..self.count].iter_mut() {
            x.function.trace(tracer);
        }
        // Not required, but since we are chosing not to walk those above
        // the current stack depth, it's good practice to blank those values out
        for x in self.stack[self.count..].iter_mut() {
            x.function = Value::new_none();
            x.file = None;
        }
    }
}

impl<'v> CallStack<'v> {
    /// Push an element to the stack. It is important the each `push` is paired
    /// with a `pop`.
    pub(crate) fn push(
        &mut self,
        function: Value<'v>,
        span: Span,
        file: Option<&'v CodeMap>,
    ) -> anyhow::Result<()> {
        if unlikely(self.count >= MAX_CALLSTACK_RECURSION) {
            return Err(ControlError::TooManyRecursionLevel.into());
        }
        self.stack[self.count] = CheapFrame {
            function,
            file,
            span,
        };
        self.count += 1;
        Ok(())
    }

    /// Remove the top element from the stack. Called after `push`.
    pub(crate) fn pop(&mut self) {
        debug_assert!(self.count >= 1);
        // We could clear the elements, but don't need to bother
        self.count -= 1;
    }

    /// The location at the top of the stack. May be `None` if
    /// either there the stack is empty, or the top of the stack lacks location
    /// information (e.g. called from Rust).
    pub fn top_location(&self) -> Option<FileSpan> {
        if self.count == 0 {
            None
        } else {
            self.stack[self.count - 1].location()
        }
    }

    pub fn to_diagnostic_frames(&self) -> Vec<Frame> {
        // The first entry is just the entire module, so skip it
        self.stack[1..self.count].map(CheapFrame::to_frame)
    }

    /// List the entries on the stack as values
    pub(crate) fn to_function_values(&self) -> Vec<Value<'v>> {
        self.stack[1..self.count].map(|x| x.function)
    }
}
