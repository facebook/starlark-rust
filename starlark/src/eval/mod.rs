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

//! Evaluation environment, provide converters from Ast* element to value.
//!
//! # <a name="build_file"></a>Starlark and BUILD dialect
//!
//! All evaluation function can evaluate the full Starlark language (i.e.
//! Bazel's .bzl files) or the BUILD file dialect (i.e. used to interpret
//! Bazel's BUILD file). The BUILD dialect does not allow `def` statements.
use crate::{
    environment::{slots::LocalSlots, Globals},
    errors::Diagnostic,
    eval::scope::Scope,
    syntax::ast::AstModule,
    values::{FrozenHeap, Value, ValueRef},
};
use anyhow::anyhow;
use codemap::{CodeMap, Span};
use gazebo::prelude::*;
use std::{fmt::Debug, mem, sync::Arc};
use thiserror::Error;

pub use crate::eval::file_loader::*;
pub use context::EvaluationContext;
pub use parameters::{Parameters, ParametersCollect};
pub(crate) use scope::ScopeNames;

pub(crate) mod call_stack;
mod expr;
mod file_loader;
mod parameters;
mod scope;
mod stmt;

#[cfg(test)]
mod tests;

pub(crate) mod compr;
mod context;
pub(crate) mod def;

pub(crate) type EvalCompiled = Box<
    dyn for<'v> Fn(&mut EvaluationContext<'v, '_>) -> Result<Value<'v>, EvalException<'v>>
        + Send
        + Sync,
>;

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

#[derive(Debug, Error)]
pub(crate) enum AssignError {
    // Expression used as left value cannot be assigned
    #[error("Incorrect expression as left value")]
    IncorrectLeftValue,
    // Incorrect number of value to unpack (expected, got)
    #[error("Unpacked {1} values but expected {0}")]
    IncorrectNumberOfValueToUnpack(i32, i32),
}

/// Convert syntax error to spanned evaluation exception
fn thrw<'v, T>(
    r: anyhow::Result<T>,
    span: Span,
    context: &EvaluationContext<'v, '_>,
) -> Result<T, EvalException<'v>> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => {
            let e = Diagnostic::modify(e, |d: &mut Diagnostic| {
                d.set_span(span, context.codemap.dupe());
                d.set_call_stack(|| context.call_stack.to_diagnostic_frames());
            });
            Err(EvalException::Error(e))
        }
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
    scope: Scope<'a>,
    heap: &'a FrozenHeap,
    globals: &'a Globals,
    errors: Vec<anyhow::Error>,
    codemap: Arc<CodeMap>,
}

pub fn eval_module<'v>(
    modu: AstModule,
    context: &mut EvaluationContext<'v, '_>,
) -> anyhow::Result<Value<'v>> {
    let AstModule { codemap, statement } = modu;
    let module_env = context.assert_module_env();

    let scope = Scope::enter_module(module_env.name(), module_env.names(), &statement);

    let span = statement.span;

    let mut compiler = Compiler {
        scope,
        heap: module_env.frozen_heap(),
        globals: context.globals,
        errors: Vec::new(),
        codemap: codemap.dupe(),
    };
    let stmt = compiler.stmt(statement);

    // We want to grab the first error only, with ownership, so drop all but the first
    compiler.errors.truncate(1);
    if let Some(e) = compiler.errors.pop() {
        // Static errors, reported even if the branch is not hit
        return Err(e);
    }

    let (module_slots, local_slots) = compiler.scope.exit_module();
    module_env.slots().ensure_slots(module_slots);
    let old_locals = mem::replace(
        &mut context.local_variables,
        LocalSlots::new(vec![ValueRef::new_unassigned(); local_slots]),
    );

    // Set up the world to allow evaluation (do NOT use ? from now on)
    let old_codemap = mem::replace(&mut context.codemap, codemap.dupe());
    context
        .call_stack
        .push(Value::new_none(), Some((codemap, span)))
        .unwrap();
    if context.profiling {
        // Make sure we don't GC the excess entries
        context.disable_gc();
        context.heap.record_call_enter(Value::new_none());
    }

    // Evaluation
    let res = stmt(context);

    // Clean up the world, putting everything back
    context.call_stack.pop();
    if context.profiling {
        context.heap.record_call_exit();
        context.heap.write_profile("starlark_profile.csv").unwrap();
    }
    context.codemap = old_codemap;
    context.local_variables = old_locals;

    // Return the result of evaluation
    Ok(res?)
}

pub fn eval_function<'v>(
    function: Value<'v>,
    positional: &[Value<'v>],
    named: &[(&str, Value<'v>)],
    context: &mut EvaluationContext<'v, '_>,
) -> anyhow::Result<Value<'v>> {
    context.with_call_stack(function, None, |context| {
        let mut invoker = function.new_invoker(context.heap)?;
        for x in positional {
            invoker.push_pos(*x);
        }
        for (s, x) in named {
            invoker.push_named(s, context.heap.alloc(*s).get_hashed()?, *x);
        }
        invoker.invoke(function, None, context)
    })
}
