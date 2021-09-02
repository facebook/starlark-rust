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

use crate::eval::{
    compiler::{
        scope::{CstStmt, ScopeId},
        Compiler, EvalException,
    },
    Evaluator,
};

impl Compiler<'_> {
    pub(crate) fn eval_module<'v>(
        &mut self,
        stmt: CstStmt,
        evaluator: &mut Evaluator<'v, '_>,
    ) -> Result<(), EvalException<'v>> {
        self.enter_scope(ScopeId::module());
        let stmt = self.stmt(stmt, true);
        self.exit_scope();
        assert!(self.locals.is_empty());
        stmt(evaluator)
    }
}
