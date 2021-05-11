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

//! Evaluate some code, typically done by creating an [`Evaluator`], then calling
//! [`eval_module`](Evaluator::eval_module).

use crate::{
    environment::slots::LocalSlots,
    eval::compiler::{scope::Scope, Compiler},
    syntax::ast::AstModule,
    values::{Value, ValueRef},
};
use gazebo::prelude::*;
use std::mem;

pub use crate::eval::file_loader::*;
pub(crate) use compiler::scope::ScopeNames;
pub use evaluator::Evaluator;
pub(crate) use parameters::ParametersCollect;
pub use parameters::{ParametersParser, ParametersSpec};

pub(crate) mod call_stack;
mod compiler;
mod evaluator;
mod file_loader;
pub(crate) mod fragment;
mod parameters;
mod stmt_profile;

#[cfg(test)]
mod tests;

impl<'v, 'a> Evaluator<'v, 'a> {
    /// Evaluate an [`AstModule`] with this [`Evaluator`], modifying the in-scope
    /// [`Module`](crate::environment::Module) as appropriate.
    pub fn eval_module(&mut self, ast: AstModule) -> anyhow::Result<Value<'v>> {
        let AstModule { codemap, statement } = ast;
        let module_env = self.assert_module_env();

        let scope = Scope::enter_module(module_env.names(), &statement);

        let span = statement.span;

        let mut compiler = Compiler {
            scope,
            heap: module_env.frozen_heap(),
            globals: self.globals,
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
            &mut self.local_variables,
            LocalSlots::new(vec![ValueRef::new_unassigned(); local_slots]),
        );

        // Set up the world to allow evaluation (do NOT use ? from now on)
        let old_codemap = self.set_codemap(codemap.dupe());
        self.call_stack
            .push(Value::new_none(), Some((codemap, span)))
            .unwrap();
        if self.profiling {
            self.heap.record_call_enter(Value::new_none());
        }

        // Evaluation
        let res = stmt(self);

        // Clean up the world, putting everything back
        self.call_stack.pop();
        if self.profiling {
            self.heap.record_call_exit();
        }
        self.set_codemap(old_codemap);
        self.local_variables = old_locals;

        // Return the result of evaluation
        Ok(res?)
    }

    /// Evaluate a function stored in a [`Value`], passing in `positional` and `named` arguments.
    pub fn eval_function(
        &mut self,
        function: Value<'v>,
        positional: &[Value<'v>],
        named: &[(&str, Value<'v>)],
    ) -> anyhow::Result<Value<'v>> {
        self.with_call_stack(function, None, |context| {
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
}
