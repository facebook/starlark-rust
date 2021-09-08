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
    environment::{Globals, Module},
    errors::Diagnostic,
    eval::{
        compiler::scope::{ScopeData, ScopeId},
        Evaluator, ScopeNames,
    },
    values::{FrozenValue, Value},
};
use anyhow::anyhow;
use gazebo::prelude::*;
use once_cell::sync::Lazy;
use std::{fmt::Debug, mem};

pub(crate) type ExprCompiled = Box<
    dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Value<'v>, ExprEvalException> + Send + Sync,
>;
pub(crate) enum ExprCompiledValue {
    Value(FrozenValue),
    Compiled(ExprCompiled),
}

impl ExprCompiledValue {
    pub fn as_value(&self) -> Option<FrozenValue> {
        match self {
            Self::Value(x) => Some(*x),
            Self::Compiled(_) => None,
        }
    }

    pub fn as_compiled(self) -> ExprCompiled {
        match self {
            Self::Value(x) => box move |_| Ok(x.to_value()),
            Self::Compiled(x) => x,
        }
    }
}

pub(crate) type StmtCompiled =
    Box<dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>> + Send + Sync>;

enum SmallVec1<T> {
    Empty,
    One(T),
    Many(Vec<T>),
}

impl<T> SmallVec1<T> {
    fn extend(&mut self, stmts: SmallVec1<T>) {
        *self = match (mem::replace(self, SmallVec1::Empty), stmts) {
            (SmallVec1::Empty, right) => right,
            (left, SmallVec1::Empty) => left,
            (SmallVec1::One(left), SmallVec1::One(right)) => SmallVec1::Many(vec![left, right]),
            (SmallVec1::One(left), SmallVec1::Many(mut right)) => {
                right.insert(0, left);
                SmallVec1::Many(right)
            }
            (SmallVec1::Many(mut left), SmallVec1::One(right)) => {
                left.push(right);
                SmallVec1::Many(left)
            }
            (SmallVec1::Many(mut left), SmallVec1::Many(right)) => {
                left.extend(right);
                SmallVec1::Many(left)
            }
        }
    }
}

pub(crate) struct StmtsCompiled(SmallVec1<StmtCompiled>);

impl StmtsCompiled {
    pub(crate) fn empty() -> StmtsCompiled {
        StmtsCompiled(SmallVec1::Empty)
    }

    pub(crate) fn one(stmt: StmtCompiled) -> StmtsCompiled {
        StmtsCompiled(SmallVec1::One(stmt))
    }

    pub(crate) fn is_empty(&self) -> bool {
        match &self.0 {
            SmallVec1::Empty => true,
            SmallVec1::One(_) => false,
            SmallVec1::Many(stmts) => {
                debug_assert!(stmts.len() > 1);
                false
            }
        }
    }

    pub(crate) fn extend(&mut self, right: StmtsCompiled) {
        self.0.extend(right.0);
    }

    pub(crate) fn as_compiled(self) -> StmtCompiled {
        match self.0 {
            SmallVec1::Empty => box |_eval| Ok(()),
            SmallVec1::One(stmt) => stmt,
            SmallVec1::Many(vec) => {
                debug_assert!(vec.len() > 1);
                box move |eval| {
                    for stmt in &vec {
                        stmt(eval)?;
                    }
                    Ok(())
                }
            }
        }
    }
}

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

impl<'v> From<anyhow::Error> for EvalException<'v> {
    fn from(x: anyhow::Error) -> Self {
        Self::Error(x)
    }
}

impl<'v> From<ExprEvalException> for EvalException<'v> {
    fn from(ExprEvalException(e): ExprEvalException) -> Self {
        Self::Error(e)
    }
}

// Make sure the error-path doesn't get inlined into the normal-path execution
#[cold]
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

#[cold]
#[inline(never)]
fn expr_throw_error<'v, T>(
    e: anyhow::Error,
    span: Span,
    eval: &Evaluator<'v, '_>,
) -> Result<T, ExprEvalException> {
    let e = Diagnostic::modify(e, |d: &mut Diagnostic| {
        d.set_span(span, eval.codemap.dupe());
        d.set_call_stack(|| eval.call_stack.to_diagnostic_frames());
    });
    Err(ExprEvalException(e))
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

/// Convert syntax error to spanned evaluation exception
pub(crate) fn expr_throw<'v, T>(
    r: anyhow::Result<T>,
    span: Span,
    eval: &Evaluator<'v, '_>,
) -> Result<T, ExprEvalException> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => expr_throw_error(e, span, eval),
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
    pub(crate) scope_data: ScopeData,
    pub(crate) locals: Vec<ScopeId>,
    pub(crate) module_env: &'a Module,
    pub(crate) codemap: CodeMap,
    pub(crate) constants: Constants,
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
