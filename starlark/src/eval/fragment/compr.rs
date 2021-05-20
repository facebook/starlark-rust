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

use crate::{
    codemap::Span,
    collections::SmallMap,
    eval::{
        compiler::{thrw, Compiler, EvalException, ExprCompiled},
        fragment::stmt::AssignCompiled,
        runtime::evaluator::Evaluator,
    },
    syntax::ast::{AstExpr, Clause, ForClause},
    values::{dict::Dict, Value},
};
use std::mem;

impl Compiler<'_> {
    pub fn list_comprehension(
        &mut self,
        x: AstExpr,
        for_: ForClause,
        clauses: Vec<Clause>,
    ) -> ExprCompiled {
        self.scope.enter_compr();
        let clauses = compile_clauses(for_, clauses, self);
        let x = self.expr(x);
        self.scope.exit_compr();
        eval_list(x, clauses)
    }

    pub fn dict_comprehension(
        &mut self,
        k: AstExpr,
        v: AstExpr,
        for_: ForClause,
        clauses: Vec<Clause>,
    ) -> ExprCompiled {
        self.scope.enter_compr();
        let clauses = compile_clauses(for_, clauses, self);
        let k = self.expr(k);
        let v = self.expr(v);
        self.scope.exit_compr();
        eval_dict(k, v, clauses)
    }
}

/// Peel the final if's from clauses, and return them (in the order they started), plus the next for you get to
fn compile_ifs(
    clauses: &mut Vec<Clause>,
    compiler: &mut Compiler,
) -> (Option<ForClause>, Vec<ExprCompiled>) {
    let mut ifs = Vec::new();
    while let Some(x) = clauses.pop() {
        match x {
            Clause::For(f) => {
                ifs.reverse();
                return (Some(f), ifs);
            }
            Clause::If(x) => {
                ifs.push(compiler.expr(x));
            }
        }
    }
    ifs.reverse();
    (None, ifs)
}

fn compile_clauses(
    for_: ForClause,
    mut clauses: Vec<Clause>,
    compiler: &mut Compiler,
) -> Vec<ClauseCompiled> {
    // The first for.over is scoped before we enter the list comp
    let over_span = for_.over.span;
    let over = compiler.expr(for_.over);

    // Now everything else must be compiled with all the for variables in scope
    compiler.scope.add_compr(&for_.var);
    for x in &clauses {
        if let Clause::For(x) = x {
            compiler.scope.add_compr(&x.var);
        }
    }

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

fn eval_list(x: ExprCompiled, clauses: Vec<ClauseCompiled>) -> ExprCompiled {
    let clauses = eval_one_dimensional_comprehension_list(clauses, box move |me, eval| {
        let x = x(eval)?;
        me.push(x);
        Ok(())
    });

    box move |eval| {
        let mut r = Vec::new();
        clauses(&mut r, eval)?;
        Ok(eval.heap().alloc(r))
    }
}

fn eval_dict(k: ExprCompiled, v: ExprCompiled, clauses: Vec<ClauseCompiled>) -> ExprCompiled {
    let clauses = eval_one_dimensional_comprehension_dict(clauses, box move |me, eval| {
        let k = k(eval)?;
        let v = v(eval)?;
        me.insert_hashed(k.get_hashed()?, v);
        Ok(())
    });

    box move |eval| {
        let mut r = SmallMap::new();
        clauses(&mut r, eval)?;
        Ok(eval.heap().alloc(Dict::new(r)))
    }
}

struct ClauseCompiled {
    var: AssignCompiled,
    over: ExprCompiled,
    over_span: Span,
    ifs: Vec<ExprCompiled>,
}

// FIXME: These two expressions are identical, but I need higher-kinded
// lifetimes to express it :(

fn eval_one_dimensional_comprehension_dict(
    mut clauses: Vec<ClauseCompiled>,
    add: Box<
        dyn for<'v> Fn(
                &mut SmallMap<Value<'v>, Value<'v>>,
                &mut Evaluator<'v, '_>,
            ) -> Result<(), EvalException<'v>>
            + Send
            + Sync,
    >,
) -> Box<
    dyn for<'v> Fn(
            &mut SmallMap<Value<'v>, Value<'v>>,
            &mut Evaluator<'v, '_>,
        ) -> Result<(), EvalException<'v>>
        + Send
        + Sync,
> {
    if let Some(c) = clauses.pop() {
        let rest = eval_one_dimensional_comprehension_dict(clauses, add);
        box move |accumulator, eval| {
            // println!("eval1 {:?} {:?}", ***e, clauses);
            let iterable = (c.over)(eval)?;
            let freeze_for_iteration = iterable.get_aref();
            'f: for i in &thrw(iterable.iterate(eval.heap()), c.over_span, eval)? {
                (c.var)(i, eval)?;
                for ifc in &c.ifs {
                    if !ifc(eval)?.to_bool() {
                        continue 'f;
                    }
                }
                rest(accumulator, eval)?;
            }
            mem::drop(freeze_for_iteration);
            Ok(())
        }
    } else {
        add
    }
}

fn eval_one_dimensional_comprehension_list(
    mut clauses: Vec<ClauseCompiled>,
    add: Box<
        dyn for<'v> Fn(&mut Vec<Value<'v>>, &mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>>
            + Send
            + Sync,
    >,
) -> Box<
    dyn for<'v> Fn(&mut Vec<Value<'v>>, &mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>>
        + Send
        + Sync,
> {
    if let Some(c) = clauses.pop() {
        let rest = eval_one_dimensional_comprehension_list(clauses, add);
        box move |accumulator, eval| {
            // println!("eval1 {:?} {:?}", ***e, clauses);
            let iterable = (c.over)(eval)?;
            let freeze_for_iteration = iterable.get_aref();
            'f: for i in &thrw(iterable.iterate(eval.heap()), c.over_span, eval)? {
                (c.var)(i, eval)?;
                for ifc in &c.ifs {
                    if !ifc(eval)?.to_bool() {
                        continue 'f;
                    }
                }
                rest(accumulator, eval)?;
            }
            mem::drop(freeze_for_iteration);
            Ok(())
        }
    } else {
        add
    }
}
