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

//! Evaluation of an expression.
use crate::{
    codemap::{Span, Spanned},
    collections::{Hashed, SmallMap},
    environment::EnvironmentError,
    errors::Diagnostic,
    eval::{evaluator::Evaluator, scope::Slot, thrw, Compiler, EvalCompiled, EvalException},
    syntax::ast::{Argument, AstExpr, AstLiteral, BinOp, Expr, Stmt, Visibility},
    values::{
        dict::FrozenDict, fast_string, function::WrappedMethod, list::FrozenList, FrozenHeap,
        FrozenValue, *,
    },
};
use either::Either;
use function::{FunctionInvoker, NativeAttribute};
use gazebo::prelude::*;
use std::{cmp::Ordering, collections::HashMap};
use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub(crate) enum EvalError {
    #[error("Dictionary key repeated for `{0}`")]
    DuplicateDictionaryKey(String),
}

fn eval_compare(
    span: Span,
    l: EvalCompiled,
    r: EvalCompiled,
    cmp: fn(Ordering) -> bool,
) -> EvalCompiled {
    box move |context| {
        Ok(Value::new_bool(cmp(thrw(
            l(context)?.compare(r(context)?),
            span,
            context,
        )?)))
    }
}

fn eval_equals(
    span: Span,
    l: EvalCompiled,
    r: EvalCompiled,
    cmp: fn(bool) -> bool,
) -> EvalCompiled {
    box move |context| {
        Ok(Value::new_bool(cmp(thrw(
            l(context)?.equals(r(context)?),
            span,
            context,
        )?)))
    }
}

fn eval_slice(
    span: Span,
    collection: EvalCompiled,
    start: Option<EvalCompiled>,
    stop: Option<EvalCompiled>,
    stride: Option<EvalCompiled>,
) -> EvalCompiled {
    box move |context| {
        let collection = collection(context)?;
        let start = match start {
            Some(ref e) => Some(e(context)?),
            None => None,
        };
        let stop = match stop {
            Some(ref e) => Some(e(context)?),
            None => None,
        };
        let stride = match stride {
            Some(ref e) => Some(e(context)?),
            None => None,
        };
        thrw(
            collection.slice(start, stop, stride, context.heap),
            span,
            context,
        )
    }
}

enum ArgCompiled {
    Pos(EvalCompiled),
    Named(String, Hashed<FrozenValue>, EvalCompiled),
    Args(EvalCompiled),
    KWArgs(EvalCompiled),
}

fn eval_call(
    span: Span,
    args: Vec<ArgCompiled>,
) -> impl for<'v> Fn(
    FunctionInvoker<'v, '_>,
    Value<'v>,
    &mut Evaluator<'v, '_>,
) -> Result<Value<'v>, EvalException<'v>> {
    move |mut invoker, function, context| {
        for x in &args {
            match x {
                ArgCompiled::Pos(expr) => invoker.push_pos(expr(context)?),
                ArgCompiled::Named(k, kk, expr) => {
                    invoker.push_named(k, kk.to_hashed_value(), expr(context)?)
                }
                ArgCompiled::Args(expr) => invoker.push_args(expr(context)?, context.heap),
                ArgCompiled::KWArgs(expr) => invoker.push_kwargs(expr(context)?),
            }
        }

        let res = invoker.invoke(function, Some(span), context);
        thrw(res, span, context)
    }
}

fn eval_dot(
    span: Span,
    e: EvalCompiled,
    s: String,
) -> impl for<'v> Fn(
    &mut Evaluator<'v, '_>,
) -> Result<Either<Value<'v>, WrappedMethod<'v>>, EvalException<'v>> {
    move |context| {
        let left = e(context)?;
        let (attr_type, v) = thrw(left.get_attr(&s, context.heap), span, context)?;
        if attr_type == AttrType::Field {
            Ok(Either::Left(v))
        } else if let Some(v_attr) = v.downcast_ref::<NativeAttribute>() {
            thrw(v_attr.call(left, context), span, context).map(Either::Left)
        } else {
            // Insert self so the method see the object it is acting on
            Ok(Either::Right(WrappedMethod::new(left, v)))
        }
    }
}

impl Compiler<'_> {
    fn exprs(
        &mut self,
        v: Vec<AstExpr>,
    ) -> Box<
        dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Vec<Value<'v>>, EvalException<'v>>
            + Send
            + Sync,
    > {
        let v = v.into_map(|x| self.expr(x));
        box move |context| {
            let mut r = Vec::with_capacity(v.len());
            for s in &v {
                r.push(s(context)?)
            }
            Ok(r)
        }
    }
}

impl AstLiteral {
    fn compile(&self, heap: &FrozenHeap) -> FrozenValue {
        match self {
            AstLiteral::IntLiteral(i) => FrozenValue::new_int(i.node),
            AstLiteral::StringLiteral(x) => heap.alloc(x.node.as_str()),
        }
    }
}

impl Expr {
    fn unpack_immutable_literal(&self) -> Option<&AstLiteral> {
        match self {
            Expr::Literal(x) => match x {
                AstLiteral::IntLiteral(_) => Some(x),
                AstLiteral::StringLiteral(_) => Some(x),
            },
            _ => None,
        }
    }

    fn unpack_int_literal(&self) -> Option<i32> {
        match self {
            Expr::Literal(AstLiteral::IntLiteral(i)) => Some(i.node),
            _ => None,
        }
    }

    fn unpack_string_literal(&self) -> Option<&str> {
        match self {
            Expr::Literal(AstLiteral::StringLiteral(i)) => Some(&i.node),
            _ => None,
        }
    }

    // Does an entire sequence of additions reduce to a string literal
    fn reduces_to_string<'a>(
        mut op: BinOp,
        mut left: &'a AstExpr,
        mut right: &'a AstExpr,
    ) -> Option<String> {
        let mut results = Vec::new();
        loop {
            if op != BinOp::Addition {
                return None;
            }
            // a + b + c  associates as  (a + b) + c
            let x = right.unpack_string_literal()?;
            results.push(x.to_owned());
            match &left.node {
                Expr::Op(left2, op2, right2) => {
                    op = *op2;
                    left = left2;
                    right = right2;
                }
                _ => {
                    let x = left.unpack_string_literal()?;
                    results.push(x.to_owned());
                    break;
                }
            }
        }
        results.reverse();
        Some(results.concat())
    }

    // Collect variables defined in an expression on the LHS of an assignment (or
    // for variable etc)
    pub(crate) fn collect_defines_lvalue<'a>(
        expr: &'a AstExpr,
        result: &mut HashMap<&'a str, Visibility>,
    ) {
        expr.node.visit_expr_lvalue(|x| {
            result.insert(&x.node, Visibility::Public);
        })
    }
}

impl Compiler<'_> {
    pub fn expr_opt(&mut self, expr: Option<Box<AstExpr>>) -> Option<EvalCompiled> {
        expr.map(|v| self.expr(*v))
    }

    pub fn expr(&mut self, expr: AstExpr) -> EvalCompiled {
        // println!("compile {}", expr.node);
        let span = expr.span;
        match expr.node {
            Expr::Identifier(ident) => {
                let name = ident.node;
                let span = ident.span;
                match self.scope.get_name(&name) {
                    Some(Slot::Local(slot)) => {
                        // We can't look up the local variabless in advance, because they are different each time
                        // we go through a new function call.
                        box move |context| thrw(context.get_slot_local(slot, &name), span, context)
                    }
                    Some(Slot::Module(slot)) => {
                        // We can't look up the module variables in advance because the first time around they are
                        // mutables, but after freezing they point at a different set of frozen slots.
                        box move |context| thrw(context.get_slot_module(slot, &name), span, context)
                    }
                    None => {
                        // Must be a global, since we know all variables
                        match self.globals.get_frozen(&name) {
                            Some(v) => box move |_| Ok(v.to_value()),
                            None => {
                                let name = name.to_owned();
                                let codemap = self.codemap.dupe();
                                let mk_err = move || {
                                    Diagnostic::new(
                                        EnvironmentError::VariableNotFound(name.clone()),
                                        span,
                                        codemap.dupe(),
                                    )
                                };
                                self.errors.push(mk_err());
                                box move |_| Err(EvalException::Error(mk_err()))
                            }
                        }
                    }
                }
            }
            Expr::Tuple(exprs) => {
                let exprs = self.exprs(exprs);
                box move |context| Ok(context.heap.alloc(tuple::Tuple::new(exprs(context)?)))
            }
            Expr::Lambda(params, box inner) => {
                let suite = Spanned {
                    span: expr.span,
                    node: Stmt::Return(Some(inner)),
                };
                self.function("lambda", params, None, suite)
            }
            Expr::List(exprs) => {
                if let Some(lits) = exprs
                    .iter()
                    .map(|e| e.unpack_immutable_literal())
                    .collect::<Option<Vec<_>>>()
                {
                    let vals: Vec<FrozenValue> = lits.map(|v| v.compile(self.heap));
                    let result = self.heap.alloc(FrozenList { content: vals });
                    box move |context| Ok(context.heap.alloc_thaw_on_write(result))
                } else {
                    let exprs = self.exprs(exprs);
                    box move |context| Ok(context.heap.alloc(exprs(context)?))
                }
            }
            Expr::Dict(exprs) => {
                if let Some(lits) = exprs
                    .iter()
                    .map(|(k, v)| {
                        Some((k.unpack_immutable_literal()?, v.unpack_immutable_literal()?))
                    })
                    .collect::<Option<Vec<_>>>()
                {
                    let mut res = SmallMap::new();
                    for (k, v) in lits.iter() {
                        res.insert_hashed(
                            k.compile(self.heap)
                                .get_hashed()
                                .expect("Dictionary literals are hashable"),
                            v.compile(self.heap),
                        );
                    }
                    // If we lost some elements, then there are duplicates, so don't take the fast-literal
                    // path and go down the slow runtime path (which will raise the error).
                    // We have a lint that will likely fire on this issue (and others).
                    if res.len() == lits.len() {
                        let result = self.heap.alloc(FrozenDict::new(res));
                        return box move |context| Ok(context.heap.alloc_thaw_on_write(result));
                    }
                }

                let v = exprs.into_map(|(k, v)| (self.expr(k), self.expr(v)));
                box move |context| {
                    let mut r = SmallMap::with_capacity(v.len());
                    for (k, v) in v.iter() {
                        let k = k(context)?;
                        if r.insert_hashed(k.get_hashed()?, v(context)?).is_some() {
                            thrw(
                                Err(EvalError::DuplicateDictionaryKey(k.to_string()).into()),
                                span,
                                context,
                            )?;
                        }
                    }
                    Ok(context.heap.alloc(dict::Dict::new(r)))
                }
            }
            Expr::If(box (cond, then_expr, else_expr)) => {
                let cond = self.expr(cond);
                let then_expr = self.expr(then_expr);
                let else_expr = self.expr(else_expr);
                box move |context| {
                    if cond(context)?.to_bool() {
                        then_expr(context)
                    } else {
                        else_expr(context)
                    }
                }
            }
            Expr::Dot(left, right) => {
                let left = self.expr(*left);
                let res = eval_dot(expr.span, left, right.node);
                box move |context| match res(context)? {
                    Either::Left(v) => Ok(v),
                    Either::Right(v) => Ok(context.heap.alloc(v)),
                }
            }
            Expr::Call(left, args) => {
                let args = args.into_map(|x| match x.node {
                    Argument::Positional(x) => ArgCompiled::Pos(self.expr(x)),
                    Argument::Named(name, value) => {
                        let name_value = self
                            .heap
                            .alloc(name.node.as_str())
                            .get_hashed()
                            .expect("String is Hashable");
                        ArgCompiled::Named(name.node, name_value, self.expr(value))
                    }
                    Argument::ArgsArray(x) => ArgCompiled::Args(self.expr(x)),
                    Argument::KWArgsDict(x) => ArgCompiled::KWArgs(self.expr(x)),
                });
                let call = eval_call(span, args);
                match left.node {
                    Expr::Dot(e, s) => {
                        let e = self.expr(*e);
                        let dot = eval_dot(span, e, s.node);
                        box move |context| match dot(context)? {
                            Either::Left(function) => {
                                let invoker =
                                    thrw(function.new_invoker(context.heap), span, context)?;
                                call(invoker, function, context)
                            }
                            Either::Right(wrapper) => {
                                let invoker = thrw(wrapper.invoke(context.heap), span, context)?;
                                call(invoker, wrapper.method, context)
                            }
                        }
                    }
                    _ => {
                        let left = self.expr(*left);
                        box move |context| {
                            let function = left(context)?;
                            let invoker = thrw(function.new_invoker(context.heap), span, context)?;
                            call(invoker, function, context)
                        }
                    }
                }
            }
            Expr::ArrayIndirection(box (array, index)) => {
                let array = self.expr(array);
                let index = self.expr(index);
                box move |context| {
                    thrw(
                        array(context)?.at(index(context)?, context.heap),
                        span,
                        context,
                    )
                }
            }
            Expr::Slice(collection, start, stop, stride) => {
                let collection = self.expr(*collection);
                let start = start.map(|x| self.expr(*x));
                let stop = stop.map(|x| self.expr(*x));
                let stride = stride.map(|x| self.expr(*x));
                eval_slice(span, collection, start, stop, stride)
            }
            Expr::Not(expr) => {
                let expr = self.expr(*expr);
                box move |context| Ok(Value::new_bool(!expr(context)?.to_bool()))
            }
            Expr::Minus(expr) => match expr.unpack_int_literal().and_then(i32::checked_neg) {
                None => {
                    let expr = self.expr(*expr);
                    box move |context| thrw(expr(context)?.minus(context.heap), span, context)
                }
                Some(x) => {
                    let val = FrozenValue::new_int(x);
                    box move |_| Ok(Value::new_frozen(val))
                }
            },
            Expr::Plus(expr) => match expr.unpack_int_literal() {
                None => {
                    let expr = self.expr(*expr);
                    box move |context| thrw(expr(context)?.plus(context.heap), span, context)
                }
                Some(x) => {
                    let val = FrozenValue::new_int(x);
                    box move |_| Ok(Value::new_frozen(val))
                }
            },
            Expr::BitNot(expr) => {
                let expr = self.expr(*expr);
                box move |context| Ok(Value::new_int(!expr(context)?.to_int()?))
            }
            Expr::Op(left, op, right) => {
                if let Some(x) = Expr::reduces_to_string(op, &left, &right) {
                    let val = self.heap.alloc(x);
                    box move |_| Ok(Value::new_frozen(val))
                } else {
                    let l = self.expr(*left);
                    let r = self.expr(*right);
                    match op {
                        BinOp::Or => box move |context| {
                            let l = l(context)?;
                            if l.to_bool() { Ok(l) } else { r(context) }
                        },
                        BinOp::And => box move |context| {
                            let l = l(context)?;
                            Ok(if !l.to_bool() { l } else { r(context)? })
                        },
                        BinOp::EqualsTo => eval_equals(span, l, r, |x| x),
                        BinOp::Different => eval_equals(span, l, r, |x| !x),
                        BinOp::LessThan => eval_compare(span, l, r, |x| x == Ordering::Less),
                        BinOp::GreaterThan => eval_compare(span, l, r, |x| x == Ordering::Greater),
                        BinOp::LessOrEqual => eval_compare(span, l, r, |x| x != Ordering::Greater),
                        BinOp::GreaterOrEqual => eval_compare(span, l, r, |x| x != Ordering::Less),
                        BinOp::In => box move |context| {
                            thrw(
                                r(context)?.is_in(l(context)?).map(Value::new_bool),
                                span,
                                context,
                            )
                        },
                        BinOp::NotIn => box move |context| {
                            thrw(
                                r(context)?.is_in(l(context)?).map(|x| Value::new_bool(!x)),
                                span,
                                context,
                            )
                        },
                        BinOp::Subtraction => box move |context| {
                            thrw(l(context)?.sub(r(context)?, context.heap), span, context)
                        },
                        BinOp::Addition => box move |context| {
                            // Addition of string is super common and pretty cheap, so have a special case for it.
                            let l = l(context)?;
                            let r = r(context)?;
                            if let Some(ls) = l.unpack_str() {
                                if let Some(rs) = r.unpack_str() {
                                    if ls.is_empty() {
                                        return Ok(r);
                                    } else if rs.is_empty() {
                                        return Ok(l);
                                    } else {
                                        return Ok(context.heap.alloc(fast_string::append(ls, rs)));
                                    }
                                }
                            }

                            // Written using Value::add so that Rust Analyzer doesn't think it is an error.
                            thrw(Value::add(l, r, context.heap), span, context)
                        },
                        BinOp::Multiplication => box move |context| {
                            thrw(l(context)?.mul(r(context)?, context.heap), span, context)
                        },
                        BinOp::Percent => box move |context| {
                            thrw(
                                l(context)?.percent(r(context)?, context.heap),
                                span,
                                context,
                            )
                        },
                        BinOp::FloorDivision => box move |context| {
                            thrw(
                                l(context)?.floor_div(r(context)?, context.heap),
                                span,
                                context,
                            )
                        },
                        BinOp::BitAnd => {
                            box move |context| thrw(l(context)?.bit_and(r(context)?), span, context)
                        }
                        BinOp::BitOr => {
                            box move |context| thrw(l(context)?.bit_or(r(context)?), span, context)
                        }
                        BinOp::BitXor => {
                            box move |context| thrw(l(context)?.bit_xor(r(context)?), span, context)
                        }
                        BinOp::LeftShift => box move |context| {
                            thrw(l(context)?.left_shift(r(context)?), span, context)
                        },
                        BinOp::RightShift => box move |context| {
                            thrw(l(context)?.right_shift(r(context)?), span, context)
                        },
                    }
                }
            }
            Expr::ListComprehension(x, box for_, clauses) => {
                self.list_comprehension(*x, for_, clauses)
            }
            Expr::DictComprehension(box (k, v), box for_, clauses) => {
                self.dict_comprehension(k, v, for_, clauses)
            }
            Expr::Literal(x) => {
                let val = x.compile(self.heap);
                box move |_| Ok(Value::new_frozen(val))
            }
        }
    }
}
