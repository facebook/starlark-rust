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

pub(crate) mod scope;

use crate::{
    codemap::{CodeMap, Span},
    environment::Globals,
    errors::Diagnostic,
    eval::{compiler::scope::Scope, Evaluator},
    values::{FrozenHeap, FrozenValue, Value},
};
use anyhow::anyhow;
use gazebo::prelude::*;
use std::fmt::Debug;

pub(crate) type ExprCompiled = Box<
    dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Value<'v>, EvalException<'v>> + Send + Sync,
>;
pub(crate) enum ExprCompiledValue {
    Value(FrozenValue),
    Compiled(ExprCompiled),
}

impl ExprCompiledValue {
    pub fn as_compiled(self) -> ExprCompiled {
        match self {
            Self::Value(x) => box move |_| Ok(x.to_value()),
            Self::Compiled(x) => x,
        }
    }
}

pub(crate) type StmtCompiled =
    Box<dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>> + Send + Sync>;

#[derive(Debug)]
pub(crate) enum EvalException<'v> {
    // Flow control statement reached, impossible to escape with
    // since we statically check for them
    Break,
    Continue,
    Return(Value<'v>),
    // Error bubbling up
    Error(anyhow::Error),
}

impl<'v> From<anyhow::Error> for EvalException<'v> {
    fn from(x: anyhow::Error) -> Self {
        Self::Error(x)
    }
}

// Make sure the error-path doesn't get inlined into the normal-path execution
#[inline(never)]
fn throw_error<'v, T>(
    e: anyhow::Error,
    span: Span,
    eval: &Evaluator<'v, '_>,
) -> Result<T, EvalException<'v>> {
    let e = Diagnostic::modify(e, |d: &mut Diagnostic| {
        d.set_span(span, eval.codemap.dupe());
        d.set_call_stack(|| eval.call_stack.to_diagnostic_frames());
    });
    Err(EvalException::Error(e))
}

/// Convert syntax error to spanned evaluation exception
pub(crate) fn throw<'v, T>(
    r: anyhow::Result<T>,
    span: Span,
    eval: &Evaluator<'v, '_>,
) -> Result<T, EvalException<'v>> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => throw_error(e, span, eval),
    }
}

impl From<EvalException<'_>> for anyhow::Error {
    fn from(x: EvalException) -> Self {
        match x {
            EvalException::Error(e) => e,
            EvalException::Break => anyhow!("Break statement used outside of a loop"),
            EvalException::Continue => anyhow!("Continue statement used outside of a loop"),
            EvalException::Return(..) => {
                anyhow!("Return statement used outside of a function call")
            }
        }
    }
}

pub(crate) struct Compiler<'a> {
    pub(crate) scope: Scope<'a>,
    pub(crate) heap: &'a FrozenHeap,
    pub(crate) globals: &'a Globals,
    pub(crate) errors: Vec<anyhow::Error>,
    pub(crate) codemap: CodeMap,
}
