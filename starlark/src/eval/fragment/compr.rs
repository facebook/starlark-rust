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
        compiler::{
            scope::{CstExpr, CstPayload},
            throw, Compiler, EvalException, ExprCompiled, ExprCompiledValue,
        },
        fragment::{known::list_to_tuple, stmt::AssignCompiled},
        runtime::evaluator::Evaluator,
    },
    syntax::ast::{ClauseP, ForClauseP},
    values::{dict::Dict, list::List, Value},
};

impl Compiler<'_> {
    pub fn list_comprehension(
        &mut self,
        x: CstExpr,
        for_: ForClauseP<CstPayload>,
        clauses: Vec<ClauseP<CstPayload>>,
    ) -> ExprCompiledValue {
        self.scope.enter_compr();
        let clauses = compile_clauses(for_, clauses, self);
        let x = self.expr(x).as_compiled();
        self.scope.exit_compr();
        eval_list(x, clauses)
    }

    pub fn dict_comprehension(
        &mut self,
        k: CstExpr,
        v: CstExpr,
        for_: ForClauseP<CstPayload>,
        clauses: Vec<ClauseP<CstPayload>>,
    ) -> ExprCompiledValue {
        self.scope.enter_compr();
        let clauses = compile_clauses(for_, clauses, self);
        let k = self.expr(k).as_compiled();
        let v = self.expr(v).as_compiled();
        self.scope.exit_compr();
        eval_dict(k, v, clauses)
    }
}

/// Peel the final if's from clauses, and return them (in the order they started), plus the next for you get to
fn compile_ifs(
    clauses: &mut Vec<ClauseP<CstPayload>>,
    compiler: &mut Compiler,
) -> (Option<ForClauseP<CstPayload>>, Vec<ExprCompiled>) {
    let mut ifs = Vec::new();
    while let Some(x) = clauses.pop() {
        match x {
            ClauseP::For(f) => {
                ifs.reverse();
                return (Some(f), ifs);
            }
            ClauseP::If(x) => {
                ifs.push(compiler.expr(x).as_compiled());
            }
        }
    }
    ifs.reverse();
    (None, ifs)
}

fn compile_clauses(
    mut for_: ForClauseP<CstPayload>,
    mut clauses: Vec<ClauseP<CstPayload>>,
    compiler: &mut Compiler,
) -> Vec<ClauseCompiled> {
    // The first for.over is scoped before we enter the list comp
    let over_span = for_.over.span;
    let over = compiler.expr(list_to_tuple(for_.over));

    // Now everything else must be compiled with all the for variables in scope
    compiler.scope.add_compr(&mut for_.var);
    for x in &mut clauses {
        if let ClauseP::For(x) = x {
            compiler.scope.add_compr(&mut x.var);
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
                    over: over.as_compiled(),
                    over_span,
                    ifs,
                });
                return res;
            }
            Some(f) => {
                let over_span = f.over.span;
                res.push(ClauseCompiled {
                    over: compiler.expr(f.over).as_compiled(),
                    var: compiler.assign(f.var),
                    over_span,
                    ifs,
                });
            }
        }
    }
}

fn eval_list(x: ExprCompiled, mut clauses: Vec<ClauseCompiled>) -> ExprCompiledValue {
    if clauses.len() == 1 && clauses[0].ifs.is_empty() {
        let c = clauses.pop().unwrap();
        expr!("list_comp_map", |eval| {
            let iterable = (c.over)(eval)?;
            throw(
                iterable.with_iterator(eval.heap(), |it| -> Result<_, EvalException> {
                    let mut res = Vec::with_capacity(it.size_hint().0);
                    for i in it {
                        (c.var)(i, eval)?;
                        res.push(x(eval)?);
                    }
                    Ok(eval.heap().alloc(List::new(res)))
                }),
                c.over_span,
                eval,
            )??
        })
    } else {
        let clauses = eval_one_dimensional_comprehension_list(clauses, box move |me, eval| {
            let x = x(eval)?;
            me.push(x);
            Ok(())
        });
        expr!("list_comp", |eval| {
            let mut r = Vec::new();
            clauses(&mut r, eval)?;
            eval.heap().alloc(List::new(r))
        })
    }
}

fn eval_dict(k: ExprCompiled, v: ExprCompiled, clauses: Vec<ClauseCompiled>) -> ExprCompiledValue {
    let clauses = eval_one_dimensional_comprehension_dict(clauses, box move |me, eval| {
        let k = k(eval)?;
        let v = v(eval)?;
        me.insert_hashed(k.get_hashed()?, v);
        Ok(())
    });

    expr!("dict_comp", |eval| {
        let mut r = SmallMap::new();
        clauses(&mut r, eval)?;
        eval.heap().alloc(Dict::new(r))
    })
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
            'f: for i in throw(iterable.iterate(eval.heap()), c.over_span, eval)? {
                (c.var)(i, eval)?;
                for ifc in &c.ifs {
                    if !ifc(eval)?.to_bool() {
                        continue 'f;
                    }
                }
                rest(accumulator, eval)?;
            }
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
            'f: for i in throw(iterable.iterate(eval.heap()), c.over_span, eval)? {
                (c.var)(i, eval)?;
                for ifc in &c.ifs {
                    if !ifc(eval)?.to_bool() {
                        continue 'f;
                    }
                }
                rest(accumulator, eval)?;
            }
            Ok(())
        }
    } else {
        add
    }
}
