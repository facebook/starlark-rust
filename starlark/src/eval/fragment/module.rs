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
            scope::{CstLoad, CstStmt, ScopeId, Slot},
            throw, Compiler, EvalException,
        },
        Evaluator,
    },
    syntax::ast::StmtP,
};

impl Compiler<'_> {
    fn eval_load<'v>(
        &mut self,
        load: CstLoad,
        eval: &mut Evaluator<'v, '_>,
    ) -> Result<(), EvalException<'v>> {
        let name = load.node.module.node;

        let loadenv = match eval.loader.as_ref() {
            None => {
                return Err(EvalException::Error(
                    EnvironmentError::NoImportsAvailable(name).into(),
                ));
            }
            Some(load) => load.load(&name).map_err(EvalException::Error)?,
        };

        for (our_name, their_name) in load.node.args {
            let (slot, _captured) = self.scope_data.get_assign_ident_slot(&our_name);
            let slot = match slot {
                Slot::Local(..) => unreachable!("symbol need to be resolved to module"),
                Slot::Module(slot) => slot,
            };
            let value = throw(
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
    ) -> Result<(), EvalException<'v>> {
        match stmt.node {
            StmtP::Statements(stmts) => {
                for stmt in stmts {
                    self.eval_top_level_stmt(stmt, evaluator)?;
                }
                Ok(())
            }
            StmtP::Load(load) => self.eval_load(load, evaluator),
            _ => {
                let stmt = self.stmt(stmt, true).as_compiled(self);
                stmt(evaluator)
            }
        }
    }

    pub(crate) fn eval_module<'v>(
        &mut self,
        stmt: CstStmt,
        evaluator: &mut Evaluator<'v, '_>,
    ) -> Result<(), EvalException<'v>> {
        self.enter_scope(ScopeId::module());
        self.eval_top_level_stmt(stmt, evaluator)?;
        self.exit_scope();
        assert!(self.locals.is_empty());
        Ok(())
    }
}
