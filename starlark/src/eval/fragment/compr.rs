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
    collections::SmallMap,
    environment::FrozenModuleRef,
    eval::{
        compiler::{
            expr_throw,
            scope::{CstExpr, CstPayload},
            Compiler,
        },
        fragment::{
            expr::{ExprCompiled, ExprCompiledValue},
            known::list_to_tuple,
            stmt::AssignCompiledValue,
        },
        runtime::evaluator::Evaluator,
        ExprEvalException,
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
        let clauses = compile_clauses(for_, clauses, self);
        let x = self.expr(x);
        ExprCompiledValue::Compr(ComprCompiled::List(box x, clauses))
    }

    pub fn dict_comprehension(
        &mut self,
        k: CstExpr,
        v: CstExpr,
        for_: ForClauseP<CstPayload>,
        clauses: Vec<ClauseP<CstPayload>>,
    ) -> ExprCompiledValue {
        let clauses = compile_clauses(for_, clauses, self);
        let k = self.expr(k);
        let v = self.expr(v);
        ExprCompiledValue::Compr(ComprCompiled::Dict(box (k, v), clauses))
    }
}

/// Peel the final if's from clauses, and return them (in the order they started), plus the next for you get to
fn compile_ifs(
    clauses: &mut Vec<ClauseP<CstPayload>>,
    compiler: &mut Compiler,
) -> (
    Option<ForClauseP<CstPayload>>,
    Vec<Spanned<ExprCompiledValue>>,
) {
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

fn eval_list(x: &Spanned<ExprCompiledValue>, clauses: &[ClauseCompiled]) -> ExprCompiled {
    if clauses.len() == 1 && clauses[0].ifs.is_empty() {
        let c = clauses.last().unwrap();
        let ClauseCompiled {
            ref var,
            ref over,
            over_span,
            ref ifs,
        } = *c;
        assert!(ifs.is_empty());
        let x = x.as_compiled();
        let var = var.as_compiled();
        expr!("list_comp_map", over, |eval| {
            expr_throw(
                over.with_iterator(eval.heap(), |it| -> Result<_, ExprEvalException> {
                    let mut res = Vec::with_capacity(it.size_hint().0);
                    for i in it {
                        var(i, eval)?;
                        res.push(x(eval)?);
                    }
                    Ok(eval.heap().alloc(List::new(res)))
                }),
                over_span,
                eval,
            )??
        })
    } else {
        let x = x.as_compiled();
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

fn eval_dict(
    k: &Spanned<ExprCompiledValue>,
    v: &Spanned<ExprCompiledValue>,
    clauses: &[ClauseCompiled],
) -> ExprCompiled {
    let k_span = k.span;
    let k = k.as_compiled();
    let v = v.as_compiled();
    let clauses = eval_one_dimensional_comprehension_dict(clauses, box move |me, eval| {
        let k = k(eval)?;
        let v = v(eval)?;
        me.insert_hashed(expr_throw(k.get_hashed(), k_span, eval)?, v);
        Ok(())
    });

    expr!("dict_comp", |eval| {
        let mut r = SmallMap::new();
        clauses(&mut r, eval)?;
        eval.heap().alloc(Dict::new(r))
    })
}

#[derive(Clone, Debug)]
pub(crate) enum ComprCompiled {
    List(Box<Spanned<ExprCompiledValue>>, Vec<ClauseCompiled>),
    Dict(
        Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>,
        Vec<ClauseCompiled>,
    ),
}

impl ComprCompiled {
    pub(crate) fn as_compiled(&self) -> ExprCompiled {
        match *self {
            ComprCompiled::List(box ref x, ref clauses) => eval_list(x, clauses),
            ComprCompiled::Dict(box (ref k, ref v), ref clauses) => eval_dict(k, v, clauses),
        }
    }

    pub(crate) fn optimize_on_freeze(&self, module: &FrozenModuleRef) -> ExprCompiledValue {
        ExprCompiledValue::Compr(match self {
            ComprCompiled::List(box ref x, ref clauses) => ComprCompiled::List(
                box x.optimize_on_freeze(module),
                clauses.map(|c| c.optimize_on_freeze(module)),
            ),
            ComprCompiled::Dict(box (ref k, ref v), ref clauses) => ComprCompiled::Dict(
                box (k.optimize_on_freeze(module), v.optimize_on_freeze(module)),
                clauses.map(|c| c.optimize_on_freeze(module)),
            ),
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ClauseCompiled {
    var: Spanned<AssignCompiledValue>,
    over: Spanned<ExprCompiledValue>,
    over_span: Span,
    ifs: Vec<Spanned<ExprCompiledValue>>,
}

impl ClauseCompiled {
    fn optimize_on_freeze(&self, module: &FrozenModuleRef) -> ClauseCompiled {
        let ClauseCompiled {
            ref var,
            ref over,
            over_span,
            ref ifs,
        } = *self;
        ClauseCompiled {
            var: var.optimize_on_freeze(module),
            over: over.optimize_on_freeze(module),
            over_span,
            ifs: ifs.map(|e| e.optimize_on_freeze(module)),
        }
    }
}

// FIXME: These two expressions are identical, but I need higher-kinded
// lifetimes to express it :(

fn eval_one_dimensional_comprehension_dict(
    clauses: &[ClauseCompiled],
    add: Box<
        dyn for<'v> Fn(
                &mut SmallMap<Value<'v>, Value<'v>>,
                &mut Evaluator<'v, '_>,
            ) -> Result<(), ExprEvalException>
            + Send
            + Sync,
    >,
) -> Box<
    dyn for<'v> Fn(
            &mut SmallMap<Value<'v>, Value<'v>>,
            &mut Evaluator<'v, '_>,
        ) -> Result<(), ExprEvalException>
        + Send
        + Sync,
> {
    if let Some((c, clauses)) = clauses.split_last() {
        let ClauseCompiled {
            ref var,
            ref over,
            over_span,
            ref ifs,
        } = *c;
        let over = over.as_compiled();
        let var = var.as_compiled();
        let ifs = ifs.map(|c| c.as_compiled());
        let rest = eval_one_dimensional_comprehension_dict(clauses, add);
        box move |accumulator, eval| {
            // println!("eval1 {:?} {:?}", ***e, clauses);
            let iterable = over(eval)?;
            'f: for i in expr_throw(iterable.iterate(eval.heap()), over_span, eval)? {
                var(i, eval)?;
                for ifc in &ifs {
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
    clauses: &[ClauseCompiled],
    add: Box<
        dyn for<'v> Fn(&mut Vec<Value<'v>>, &mut Evaluator<'v, '_>) -> Result<(), ExprEvalException>
            + Send
            + Sync,
    >,
) -> Box<
    dyn for<'v> Fn(&mut Vec<Value<'v>>, &mut Evaluator<'v, '_>) -> Result<(), ExprEvalException>
        + Send
        + Sync,
> {
    if let Some((c, clauses)) = clauses.split_last() {
        let ClauseCompiled {
            ref var,
            ref over,
            over_span,
            ref ifs,
        } = *c;
        let over = over.as_compiled();
        let var = var.as_compiled();
        let ifs = ifs.map(|c| c.as_compiled());
        let rest = eval_one_dimensional_comprehension_list(clauses, add);
        box move |accumulator, eval| {
            // println!("eval1 {:?} {:?}", ***e, clauses);
            let iterable = over(eval)?;
            'f: for i in expr_throw(iterable.iterate(eval.heap()), over_span, eval)? {
                var(i, eval)?;
                for ifc in &ifs {
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
