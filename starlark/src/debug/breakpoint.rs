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

use crate::{
    codemap::Span,
    syntax::{
        ast::{AstStmt, Stmt},
        AstModule,
    },
};

fn go(x: &AstStmt, res: &mut Vec<Span>) {
    match &**x {
        Stmt::Statements(_) => {} // These are not interesting statements that come up
        _ => res.push(x.span),
    }
    x.visit_stmt(|x| go(x, res))
}

impl AstModule {
    /// Locations where statements occur, likely to be passed as the positions
    /// to [`before_stmt`](crate::eval::Evaluator::before_stmt).
    pub fn stmt_locations(&self) -> Vec<Span> {
        let mut res = Vec::new();
        self.statement.visit_stmt(|x| go(x, &mut res));
        res
    }
}
