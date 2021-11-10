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

//! List/dict/set comprenension evaluation.

use gazebo::prelude::*;

use crate::{
    codemap::{Span, Spanned},
    eval::{
        compiler::{
            scope::{CstExpr, CstPayload},
            Compiler,
        },
        fragment::{
            expr::ExprCompiled,
            known::list_to_tuple,
            stmt::{AssignCompiledValue, OptimizeOnFreezeContext},
        },
    },
    syntax::ast::{ClauseP, ForClauseP},
};

impl Compiler<'_, '_, '_> {
    pub fn list_comprehension(
        &mut self,
        x: CstExpr,
        for_: ForClauseP<CstPayload>,
        clauses: Vec<ClauseP<CstPayload>>,
    ) -> ExprCompiled {
        let clauses = compile_clauses(for_, clauses, self);
        let x = self.expr(x);
        ExprCompiled::Compr(ComprCompiled::List(box x, clauses))
    }

    pub fn dict_comprehension(
        &mut self,
        k: CstExpr,
        v: CstExpr,
        for_: ForClauseP<CstPayload>,
        clauses: Vec<ClauseP<CstPayload>>,
    ) -> ExprCompiled {
        let clauses = compile_clauses(for_, clauses, self);
        let k = self.expr(k);
        let v = self.expr(v);
        ExprCompiled::Compr(ComprCompiled::Dict(box (k, v), clauses))
    }
}

/// Peel the final if's from clauses, and return them (in the order they started), plus the next for you get to
fn compile_ifs(
    clauses: &mut Vec<ClauseP<CstPayload>>,
    compiler: &mut Compiler,
) -> (Option<ForClauseP<CstPayload>>, Vec<Spanned<ExprCompiled>>) {
    let mut ifs = Vec::new();
    while let Some(x) = clauses.pop() {
        match x {
            ClauseP::For(f) => {
                ifs.reverse();
                return (Some(f), ifs);
            }
            ClauseP::If(x) => {
                ifs.push(compiler.expr(x));
            }
        }
    }
    ifs.reverse();
    (None, ifs)
}

fn compile_clauses(
    for_: ForClauseP<CstPayload>,
    mut clauses: Vec<ClauseP<CstPayload>>,
    compiler: &mut Compiler,
) -> Vec<ClauseCompiled> {
    // The first for.over is scoped before we enter the list comp
    let over_span = for_.over.span;
    let over = compiler.expr(list_to_tuple(for_.over));

    // Now we want to group them into a `for`, followed by any number of `if`.
    // The evaluator wants to use pop to consume them, so reverse the order.
    let mut res = Vec::new();
    loop {
        let (next_for, ifs) = compile_ifs(&mut clauses, compiler);
        match next_for {
            None => {
                res.push(ClauseCompiled {
                    var: compiler.assign(for_.var),
                    over,
                    over_span,
                    ifs,
                });
                return res;
            }
            Some(f) => {
                let over_span = f.over.span;
                res.push(ClauseCompiled {
                    over: compiler.expr(f.over),
                    var: compiler.assign(f.var),
                    over_span,
                    ifs,
                });
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum ComprCompiled {
    List(Box<Spanned<ExprCompiled>>, Vec<ClauseCompiled>),
    Dict(
        Box<(Spanned<ExprCompiled>, Spanned<ExprCompiled>)>,
        Vec<ClauseCompiled>,
    ),
}

impl ComprCompiled {
    pub(crate) fn optimize_on_freeze(&self, ctx: &OptimizeOnFreezeContext) -> ExprCompiled {
        ExprCompiled::Compr(match self {
            ComprCompiled::List(box ref x, ref clauses) => ComprCompiled::List(
                box x.optimize_on_freeze(ctx),
                clauses.map(|c| c.optimize_on_freeze(ctx)),
            ),
            ComprCompiled::Dict(box (ref k, ref v), ref clauses) => ComprCompiled::Dict(
                box (k.optimize_on_freeze(ctx), v.optimize_on_freeze(ctx)),
                clauses.map(|c| c.optimize_on_freeze(ctx)),
            ),
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ClauseCompiled {
    pub(crate) var: Spanned<AssignCompiledValue>,
    pub(crate) over: Spanned<ExprCompiled>,
    pub(crate) over_span: Span,
    pub(crate) ifs: Vec<Spanned<ExprCompiled>>,
}

impl ClauseCompiled {
    fn optimize_on_freeze(&self, ctx: &OptimizeOnFreezeContext) -> ClauseCompiled {
        let ClauseCompiled {
            ref var,
            ref over,
            over_span,
            ref ifs,
        } = *self;
        ClauseCompiled {
            var: var.optimize_on_freeze(ctx),
            over: over.optimize_on_freeze(ctx),
            over_span,
            ifs: ifs.map(|e| e.optimize_on_freeze(ctx)),
        }
    }
}
