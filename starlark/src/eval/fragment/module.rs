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

//! Compile and evaluate module top-level statements.

use crate::{
    environment::EnvironmentError,
    eval::{
        compiler::{
            add_span_to_expr_error, expr_throw,
            scope::{CstLoad, CstStmt, ScopeId, Slot},
            Compiler, EvalException,
        },
        Evaluator,
    },
    syntax::ast::StmtP,
    values::Value,
};

impl Compiler<'_> {
    fn eval_load<'v>(
        &mut self,
        load: CstLoad,
        eval: &mut Evaluator<'v, '_>,
    ) -> Result<(), EvalException> {
        let name = load.node.module.node;

        let loadenv = match eval.loader.as_ref() {
            None => {
                return Err(add_span_to_expr_error(
                    EnvironmentError::NoImportsAvailable(name).into(),
                    load.span,
                    eval,
                ));
            }
            Some(loader) => expr_throw(loader.load(&name), load.span, eval)?,
        };

        for (our_name, their_name) in load.node.args {
            let (slot, _captured) = self.scope_data.get_assign_ident_slot(&our_name);
            let slot = match slot {
                Slot::Local(..) => unreachable!("symbol need to be resolved to module"),
                Slot::Module(slot) => slot,
            };
            let value = expr_throw(
                eval.module_env.load_symbol(&loadenv, &their_name.node),
                our_name.span.merge(their_name.span),
                eval,
            )?;
            eval.set_slot_module(slot, value)
        }

        Ok(())
    }

    fn eval_top_level_stmt<'v>(
        &mut self,
        stmt: CstStmt,
        evaluator: &mut Evaluator<'v, '_>,
    ) -> Result<Value<'v>, EvalException> {
        match stmt.node {
            StmtP::Statements(stmts) => {
                let mut last = Value::new_none();
                for stmt in stmts {
                    last = self.eval_top_level_stmt(stmt, evaluator)?;
                }
                Ok(last)
            }
            StmtP::Load(load) => {
                self.eval_load(load, evaluator)?;
                Ok(Value::new_none())
            }
            _ => {
                let stmt = self.module_top_level_stmt(stmt);
                let bc = stmt.as_bc(&self.compile_context());
                bc.run(evaluator)
            }
        }
    }

    pub(crate) fn eval_module<'v>(
        &mut self,
        stmt: CstStmt,
        evaluator: &mut Evaluator<'v, '_>,
    ) -> Result<Value<'v>, EvalException> {
        self.enter_scope(ScopeId::module());
        let value = self.eval_top_level_stmt(stmt, evaluator)?;
        self.exit_scope();
        assert!(self.locals.is_empty());
        Ok(value)
    }
}
