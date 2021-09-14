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
    codemap::{Span, Spanned},
    collections::symbol_map::Symbol,
    eval::compiler::{scope::Scope, Compiler, Constants, EvalException, ExprEvalException},
    syntax::ast::{AstModule, AstStmt, Expr, Stmt},
    values::Value,
};
use gazebo::{cast, prelude::*};
use std::{intrinsics::unlikely, mem};

use crate::{
    eval::compiler::{
        scope::{CompilerAstMap, ScopeData},
        throw_eval_exception,
    },
    values::docs::DocString,
};
pub(crate) use compiler::scope::ScopeNames;
pub(crate) use fragment::def::{Def, FrozenDef};
pub use runtime::{
    arguments::{Arguments, ParametersParser, ParametersSpec},
    evaluator::Evaluator,
    file_loader::{FileLoader, ReturnFileLoader},
};

mod compiler;
mod fragment;
mod runtime;

#[cfg(test)]
mod tests;

/// For modules, we want to capture the "last" statement in the code,
/// if it was an expression. Rather than keep track of the value of every
/// expression, instead add a fake return at the end if the final statement
/// is an expression.
fn inject_return(x: &mut AstStmt) {
    match &mut x.node {
        Stmt::Statements(xs) => {
            if let Some(x) = xs.last_mut() {
                inject_return(x)
            }
        }
        Stmt::Expression(e) => {
            let e = mem::replace(
                e,
                Spanned {
                    node: Expr::Tuple(Vec::new()),
                    span: Span::default(),
                },
            );
            x.node = Stmt::Return(Some(e));
        }
        _ => {}
    }
}

impl<'v, 'a> Evaluator<'v, 'a> {
    /// Evaluate an [`AstModule`] with this [`Evaluator`], modifying the in-scope
    /// [`Module`](crate::environment::Module) as appropriate.
    pub fn eval_module(&mut self, ast: AstModule) -> anyhow::Result<Value<'v>> {
        let AstModule {
            codemap,
            mut statement,
        } = ast;
        inject_return(&mut statement);

        let mut scope_data = ScopeData::new();

        let root_scope_id = scope_data.new_scope().0;

        let mut statement = statement.into_map_payload(&mut CompilerAstMap(&mut scope_data));

        if let Some(docstring) = DocString::extract_raw_starlark_docstring(&statement) {
            self.module_env.set_docstring(docstring)
        }

        let mut scope = Scope::enter_module(
            self.module_env.names(),
            root_scope_id,
            scope_data,
            &mut statement,
            self.globals,
            codemap.dupe(),
        );

        // We want to grab the first error only, with ownership, so drop all but the first
        scope.errors.truncate(1);
        if let Some(e) = scope.errors.pop() {
            // Static errors, reported even if the branch is not hit
            return Err(e);
        }

        let span = statement.span;

        let (module_slots, local_slots, scope_data) = scope.exit_module();

        self.module_env.slots().ensure_slots(module_slots);
        let new_locals = self.local_variables.reserve(local_slots);
        let old_locals = self.local_variables.utilise(new_locals);

        // Set up the world to allow evaluation (do NOT use ? from now on)

        // Safe because we promise to put codemap back to how it was before this function terminates.
        // See with_function_context for more safety arguments.
        let codemap = unsafe { cast::ptr_lifetime(&codemap) };

        let old_codemap = self.set_codemap(codemap);
        self.call_stack
            .push(Value::new_none(), span, Some(codemap))
            .unwrap();
        if unlikely(self.heap_or_flame_profile) {
            self.heap_profile
                .record_call_enter(Value::new_none(), self.heap());
            self.flame_profile.record_call_enter(Value::new_none());
        }

        // Evaluation
        let mut compiler = Compiler {
            scope_data,
            locals: Vec::new(),
            module_env: self.module_env,
            codemap: codemap.dupe(),
            constants: Constants::new(),
            has_before_stmt: !self.before_stmt.is_empty(),
        };

        let res = compiler.eval_module(statement, self);

        // Clean up the world, putting everything back
        self.call_stack.pop();
        if unlikely(self.heap_or_flame_profile) {
            self.heap_profile.record_call_exit(self.heap());
            self.flame_profile.record_call_exit();
        }
        self.set_codemap(old_codemap);
        self.local_variables.release(old_locals);

        // Return the result of evaluation
        match res {
            Ok(_) => Ok(Value::new_none()),
            Err(EvalException::Return(x)) => Ok(x),
            Err(e) => throw_eval_exception(e),
        }
    }

    /// Evaluate a function stored in a [`Value`], passing in `positional` and `named` arguments.
    pub fn eval_function(
        &mut self,
        function: Value<'v>,
        positional: &[Value<'v>],
        named: &[(&str, Value<'v>)],
    ) -> anyhow::Result<Value<'v>> {
        let names = named.map(|(s, _)| (Symbol::new(*s), self.heap().alloc_string_value(*s)));
        let named = named.map(|x| x.1);
        let params = Arguments {
            this: None,
            pos: positional,
            named: &named,
            names: &names,
            args: None,
            kwargs: None,
        };
        function.invoke(None, params, self)
    }
}
