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
    collections::SmallMap,
    eval::{
        context::EvaluationContext, stmt::AssignCompiled, thrw, Compiler, EvalCompiled,
        EvalException,
    },
    syntax::ast::{AstClause, AstExpr, Clause},
    values::{dict::Dict, Value},
};
use codemap::Span;
use gazebo::prelude::*;
use std::mem;

impl Compiler<'_> {
    pub fn list_comprehension(&mut self, x: AstExpr, clauses: Vec<AstClause>) -> EvalCompiled {
        self.scope.enter_compr();
        let clauses = compile_clauses(clauses, self);
        let x = self.expr(x);
        self.scope.exit_compr();
        eval_list(x, clauses)
    }

    pub fn dict_comprehension(
        &mut self,
        k: AstExpr,
        v: AstExpr,
        clauses: Vec<AstClause>,
    ) -> EvalCompiled {
        self.scope.enter_compr();
        let clauses = compile_clauses(clauses, self);
        let k = self.expr(k);
        let v = self.expr(v);
        self.scope.exit_compr();
        eval_dict(k, v, clauses)
    }
}

fn compile_clause(clause: AstClause, compiler: &mut Compiler) -> ClauseCompiled {
    let Clause { var, over, ifs } = clause.node;

    // Must be compiled without the new variables in scope
    let over_span = over.span;
    let over = compiler.expr(over);
    compiler.scope.add_compr(&var);

    // Everything after must be compiled with the new variables in scope
    let var = compiler.assign(var);
    let ifs = ifs.into_map(|expr| compiler.expr(expr));
    ClauseCompiled {
        var,
        over,
        over_span,
        ifs,
    }
}

fn compile_clauses(clauses: Vec<AstClause>, compiler: &mut Compiler) -> Vec<ClauseCompiled> {
    let mut res = clauses.into_map(|x| compile_clause(x, compiler));
    // The evaluator wants to use pop to consume them, so reverse the order
    res.reverse();
    res
}

fn eval_list(x: EvalCompiled, clauses: Vec<ClauseCompiled>) -> EvalCompiled {
    let clauses = eval_one_dimensional_comprehension_list(clauses, box move |me, context| {
        let x = x(context)?;
        me.push(x);
        Ok(())
    });

    box move |context| {
        let mut r = Vec::new();
        clauses(&mut r, context)?;
        Ok(context.heap.alloc(r))
    }
}

fn eval_dict(k: EvalCompiled, v: EvalCompiled, clauses: Vec<ClauseCompiled>) -> EvalCompiled {
    let clauses = eval_one_dimensional_comprehension_dict(clauses, box move |me, context| {
        let k = k(context)?;
        let v = v(context)?;
        me.insert_hashed(k.get_hashed()?, v);
        Ok(())
    });

    box move |context| {
        let mut r = SmallMap::new();
        clauses(&mut r, context)?;
        Ok(context.heap.alloc(Dict::new(r)))
    }
}

struct ClauseCompiled {
    var: AssignCompiled,
    over: EvalCompiled,
    over_span: Span,
    ifs: Vec<EvalCompiled>,
}

// FIXME: These two expressions are identical, but I need higher-kinded
// lifetimes to express it :(

fn eval_one_dimensional_comprehension_dict(
    mut clauses: Vec<ClauseCompiled>,
    add: Box<
        dyn for<'v> Fn(
            &mut SmallMap<Value<'v>, Value<'v>>,
            &mut EvaluationContext<'v, '_>,
        ) -> Result<(), EvalException<'v>>
            + Send
            + Sync,
    >,
) -> Box<
    dyn for<'v> Fn(
        &mut SmallMap<Value<'v>, Value<'v>>,
        &mut EvaluationContext<'v, '_>,
    ) -> Result<(), EvalException<'v>>
        + Send
        + Sync,
> {
    if let Some(c) = clauses.pop() {
        let rest = eval_one_dimensional_comprehension_dict(clauses, add);
        box move |accumulator, context| {
            // println!("eval1 {:?} {:?}", ***e, clauses);
            let iterable = (c.over)(context)?;
            let freeze_for_iteration = iterable.get_aref();
            'f: for i in &thrw(iterable.iterate(context.heap), c.over_span, context)? {
                (c.var)(i, context)?;
                for ifc in &c.ifs {
                    if !ifc(context)?.to_bool() {
                        continue 'f;
                    }
                }
                rest(accumulator, context)?;
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
        dyn for<'v> Fn(
            &mut Vec<Value<'v>>,
            &mut EvaluationContext<'v, '_>,
        ) -> Result<(), EvalException<'v>>
            + Send
            + Sync,
    >,
) -> Box<
    dyn for<'v> Fn(
        &mut Vec<Value<'v>>,
        &mut EvaluationContext<'v, '_>,
    ) -> Result<(), EvalException<'v>>
        + Send
        + Sync,
> {
    if let Some(c) = clauses.pop() {
        let rest = eval_one_dimensional_comprehension_list(clauses, add);
        box move |accumulator, context| {
            // println!("eval1 {:?} {:?}", ***e, clauses);
            let iterable = (c.over)(context)?;
            let freeze_for_iteration = iterable.get_aref();
            'f: for i in &thrw(iterable.iterate(context.heap), c.over_span, context)? {
                (c.var)(i, context)?;
                for ifc in &c.ifs {
                    if !ifc(context)?.to_bool() {
                        continue 'f;
                    }
                }
                rest(accumulator, context)?;
            }
            mem::drop(freeze_for_iteration);
            Ok(())
        }
    } else {
        add
    }
}
