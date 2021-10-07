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

use std::fmt::Debug;

use anyhow::anyhow;
use gazebo::prelude::*;
use once_cell::sync::Lazy;

use crate::{
    codemap::{CodeMap, Span},
    environment::{Globals, Module},
    errors::Diagnostic,
    eval::{
        compiler::scope::{ScopeData, ScopeId},
        Evaluator, ScopeNames,
    },
    values::{FrozenValue, Value},
};

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

/// Error of evaluation of an expression.
#[derive(Debug)]
pub(crate) struct ExprEvalException(anyhow::Error);

impl<'v> From<ExprEvalException> for EvalException<'v> {
    fn from(ExprEvalException(e): ExprEvalException) -> Self {
        Self::Error(e)
    }
}

#[cold]
#[inline(never)]
fn add_span_to_error(e: anyhow::Error, span: Span, eval: &Evaluator) -> anyhow::Error {
    Diagnostic::modify(e, |d: &mut Diagnostic| {
        d.set_span(span, eval.codemap.dupe());
        d.set_call_stack(|| eval.call_stack.to_diagnostic_frames());
    })
}

#[cold]
#[inline(never)]
pub(crate) fn add_span_to_expr_error(
    e: anyhow::Error,
    span: Span,
    eval: &Evaluator,
) -> ExprEvalException {
    ExprEvalException(add_span_to_error(e, span, eval))
}

#[cold]
#[inline(never)]
pub(crate) fn add_span_to_stmt_error<'v>(
    e: anyhow::Error,
    span: Span,
    eval: &Evaluator,
) -> EvalException<'v> {
    EvalException::Error(add_span_to_error(e, span, eval))
}

/// Convert syntax error to spanned evaluation exception
#[inline(always)]
pub(crate) fn throw<'v, T>(
    r: anyhow::Result<T>,
    span: Span,
    eval: &Evaluator<'v, '_>,
) -> Result<T, EvalException<'v>> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => Err(add_span_to_stmt_error(e, span, eval)),
    }
}

/// Convert syntax error to spanned evaluation exception
#[inline(always)]
pub(crate) fn expr_throw<'v, T>(
    r: anyhow::Result<T>,
    span: Span,
    eval: &Evaluator<'v, '_>,
) -> Result<T, ExprEvalException> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => Err(add_span_to_expr_error(e, span, eval)),
    }
}

#[cold]
#[inline(never)]
pub(crate) fn throw_eval_exception<T>(x: EvalException<'_>) -> anyhow::Result<T> {
    Err(match x {
        EvalException::Error(e) => e,
        EvalException::Break => anyhow!("Break statement used outside of a loop"),
        EvalException::Continue => anyhow!("Continue statement used outside of a loop"),
        EvalException::Return(..) => {
            anyhow!("Return statement used outside of a function call")
        }
    })
}

pub(crate) struct Compiler<'a> {
    pub(crate) scope_data: ScopeData,
    pub(crate) locals: Vec<ScopeId>,
    pub(crate) module_env: &'a Module,
    pub(crate) codemap: CodeMap,
    pub(crate) constants: Constants,
    pub(crate) has_before_stmt: bool,
}

impl Compiler<'_> {
    pub(crate) fn enter_scope(&mut self, scope_id: ScopeId) {
        self.locals.push(scope_id);
    }

    pub(crate) fn exit_scope(&mut self) -> &mut ScopeNames {
        let scope_id = self.locals.pop().unwrap();
        self.scope_data.mut_scope(scope_id)
    }
}

#[derive(Clone, Copy, Dupe)]
pub(crate) struct Constants {
    pub(crate) fn_len: FrozenValue,
    pub(crate) fn_type: FrozenValue,
}

impl Constants {
    pub fn new() -> Self {
        static RES: Lazy<Constants> = Lazy::new(|| {
            let g = Globals::standard();
            Constants {
                fn_len: g.get_frozen("len").unwrap(),
                fn_type: g.get_frozen("type").unwrap(),
            }
        });
        *Lazy::force(&RES)
    }
}
