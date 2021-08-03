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
    collections::{symbol_map::Symbol, SmallMap},
    environment::EnvironmentError,
    errors::Diagnostic,
    eval::{
        compiler::{scope::Slot, throw, Compiler, EvalException, ExprCompiled, ExprCompiledValue},
        runtime::evaluator::Evaluator,
        Parameters,
    },
    syntax::ast::{
        Argument, AstArgument, AstAssign, AstExpr, AstLiteral, BinOp, Expr, Stmt, Visibility,
    },
    values::{
        dict::Dict,
        function::{BoundMethod, NativeAttribute},
        list::List,
        tuple::{FrozenTuple, Tuple},
        AttrType, FrozenHeap, FrozenValue, Heap, Value, ValueError, ValueLike,
    },
};
use gazebo::{coerce::coerce_ref, prelude::*};
use std::{cmp::Ordering, collections::HashMap, mem::MaybeUninit};
use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub(crate) enum EvalError {
    #[error("Dictionary key repeated for `{0}`")]
    DuplicateDictionaryKey(String),
}

fn eval_compare(
    span: Span,
    l: ExprCompiledValue,
    r: ExprCompiledValue,
    cmp: fn(Ordering) -> bool,
) -> ExprCompiledValue {
    expr!("compare", l, r, |eval| {
        Value::new_bool(cmp(throw(l.compare(r), span, eval)?))
    })
}

fn eval_equals(
    span: Span,
    l: ExprCompiledValue,
    r: ExprCompiledValue,
    cmp: fn(bool) -> bool,
) -> ExprCompiledValue {
    expr!("equals", l, r, |eval| {
        Value::new_bool(cmp(throw(l.equals(r), span, eval)?))
    })
}

fn eval_slice(
    span: Span,
    collection: ExprCompiledValue,
    start: Option<ExprCompiledValue>,
    stop: Option<ExprCompiledValue>,
    stride: Option<ExprCompiledValue>,
) -> ExprCompiledValue {
    let start = start.map(ExprCompiledValue::as_compiled);
    let stop = stop.map(ExprCompiledValue::as_compiled);
    let stride = stride.map(ExprCompiledValue::as_compiled);
    expr!("slice", collection, |eval| {
        let start = match start {
            Some(ref e) => Some(e(eval)?),
            None => None,
        };
        let stop = match stop {
            Some(ref e) => Some(e(eval)?),
            None => None,
        };
        let stride = match stride {
            Some(ref e) => Some(e(eval)?),
            None => None,
        };
        throw(
            collection.slice(start, stop, stride, eval.heap()),
            span,
            eval,
        )?
    })
}

/// Conditional statements are fairly common, some have literals (or imported values)
/// and quite a few start with a `not`, so encode those options statically.
pub(crate) enum Conditional {
    True,
    False,
    Normal(ExprCompiled),
    Negate(ExprCompiled),
}

impl Compiler<'_> {
    pub fn conditional(&mut self, expr: AstExpr) -> Conditional {
        let (expect, val) = match expr {
            Spanned {
                node: Expr::Not(box expr),
                ..
            } => (false, self.expr(expr)),
            _ => (true, self.expr(expr)),
        };
        match val {
            ExprCompiledValue::Value(x) => {
                if x.get_ref().to_bool() == expect {
                    Conditional::True
                } else {
                    Conditional::False
                }
            }
            ExprCompiledValue::Compiled(v) => {
                if expect {
                    Conditional::Normal(v)
                } else {
                    Conditional::Negate(v)
                }
            }
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
            if op != BinOp::Add {
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
        expr: &'a AstAssign,
        result: &mut HashMap<&'a str, Visibility>,
    ) {
        expr.node.visit_lvalue(|x| {
            result.insert(&x.node, Visibility::Public);
        })
    }
}

#[derive(Default)]
struct ArgsCompiled {
    pos_named: Vec<ExprCompiled>,
    names: Vec<(Symbol, FrozenValue)>,
    args: Option<ExprCompiled>,
    kwargs: Option<ExprCompiled>,
}

// Helper that creates some specialised argument calls
macro_rules! args {
    ($args:ident, $e:expr) => {
        if $args.names.is_empty()
            && $args.args.is_none()
            && $args.kwargs.is_none()
            && $args.pos_named.len() <= 2
        {
            let mut args = $args;
            match args.pos_named.pop() {
                None => {
                    let $args = Args0Compiled;
                    $e
                }
                Some(a1) => match args.pos_named.pop() {
                    None => {
                        let $args = Args1Compiled(a1);
                        $e
                    }
                    Some(a2) => {
                        let $args = Args2Compiled(a2, a1);
                        $e
                    }
                },
            }
        } else {
            $e
        }
    };
}

struct Args0Compiled;

struct Args1Compiled(ExprCompiled);

struct Args2Compiled(ExprCompiled, ExprCompiled);

impl Args0Compiled {
    #[inline(always)]
    fn with_params<'v, R>(
        &self,
        this: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_>,
        f: impl FnOnce(Parameters<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        let params = Parameters {
            this,
            pos: &[],
            named: &[],
            names: &[],
            args: None,
            kwargs: None,
        };
        f(params, eval)
    }
}

impl Args1Compiled {
    #[inline(always)]
    fn with_params<'v, R>(
        &self,
        this: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_>,
        f: impl FnOnce(Parameters<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        let params = Parameters {
            this,
            pos: &[self.0(eval)?],
            named: &[],
            names: &[],
            args: None,
            kwargs: None,
        };
        f(params, eval)
    }
}

impl Args2Compiled {
    #[inline(always)]
    fn with_params<'v, R>(
        &self,
        this: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_>,
        f: impl FnOnce(Parameters<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        let params = Parameters {
            this,
            pos: &[self.0(eval)?, self.1(eval)?],
            named: &[],
            names: &[],
            args: None,
            kwargs: None,
        };
        f(params, eval)
    }
}

impl ArgsCompiled {
    #[inline(always)]
    fn with_params<'v, R>(
        &self,
        this: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_>,
        f: impl FnOnce(Parameters<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        eval.alloca_uninit(self.pos_named.len(), |xs, eval| {
            // because Value has no drop, we don't need to worry about failures before assume_init
            for (x, arg) in xs.iter_mut().zip(&self.pos_named) {
                x.write(arg(eval)?);
            }
            // because we allocated `pos_named` elements and filled them all, we can assume it is now init
            let xs = unsafe { MaybeUninit::slice_assume_init_ref(xs) };

            let args = match &self.args {
                None => None,
                Some(f) => Some(f(eval)?),
            };
            let kwargs = match &self.kwargs {
                None => None,
                Some(f) => Some(f(eval)?),
            };
            let (pos, named) = &xs.split_at(xs.len() - self.names.len());
            let params = Parameters {
                this,
                pos,
                named,
                names: coerce_ref(&self.names),
                args,
                kwargs,
            };
            f(params, eval)
        })
    }
}

fn get_attr_hashed<'v>(
    x: Value<'v>,
    attribute: &Symbol,
    heap: &'v Heap,
) -> anyhow::Result<(AttrType, Value<'v>)> {
    let aref = x.get_ref();
    if let Some(methods) = aref.get_methods() {
        if let Some(v) = methods.get_frozen_symbol(attribute) {
            return Ok((AttrType::Method, v.to_value()));
        }
    }
    match aref.get_attr(attribute.as_str(), heap) {
        None => ValueError::unsupported_owned(
            aref.get_type(),
            &format!(".{}", attribute.as_str()),
            None,
        ),
        Some(x) => Ok((AttrType::Field, x)),
    }
}

impl Compiler<'_> {
    pub fn expr_opt(&mut self, expr: Option<Box<AstExpr>>) -> Option<ExprCompiledValue> {
        expr.map(|v| self.expr(*v))
    }

    fn args(&mut self, args: Vec<AstArgument>) -> ArgsCompiled {
        let mut res = ArgsCompiled::default();
        for x in args {
            match x.node {
                Argument::Positional(x) => res.pos_named.push(self.expr(x).as_compiled()),
                Argument::Named(name, value) => {
                    let fv = self.heap.alloc(name.node.as_str());
                    res.names.push((Symbol::new(&name.node), fv));
                    res.pos_named.push(self.expr(value).as_compiled());
                }
                Argument::Args(x) => res.args = Some(self.expr(x).as_compiled()),
                Argument::KwArgs(x) => res.kwargs = Some(self.expr(x).as_compiled()),
            }
        }
        res
    }

    pub fn expr(&mut self, expr: AstExpr) -> ExprCompiledValue {
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
                        expr!("local", |eval| throw(
                            eval.get_slot_local(slot, &name),
                            span,
                            eval
                        )?)
                    }
                    Some(Slot::Module(slot)) => {
                        // We can't look up the module variables in advance because the first time around they are
                        // mutables, but after freezing they point at a different set of frozen slots.
                        expr!("module", |eval| throw(
                            eval.get_slot_module(slot),
                            span,
                            eval
                        )?)
                    }
                    None => {
                        // Must be a global, since we know all variables
                        match self.globals.get_frozen(&name) {
                            Some(v) => value!(v),
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
                                ExprCompiledValue::Compiled(box move |_eval| {
                                    Err(EvalException::Error(mk_err()))
                                })
                            }
                        }
                    }
                }
            }
            Expr::Lambda(params, box inner) => {
                let suite = Spanned {
                    span: expr.span,
                    node: Stmt::Return(Some(inner)),
                };
                self.function("lambda", params, None, suite)
            }
            Expr::Tuple(exprs) => {
                let xs = exprs.into_map(|x| self.expr(x));
                if xs.iter().all(|x| x.as_value().is_some()) {
                    let content = xs.map(|v| v.as_value().unwrap());
                    let result = self.heap.alloc(FrozenTuple { content });
                    value!(result)
                } else {
                    let xs = xs.into_map(|x| x.as_compiled());
                    expr!("tuple", |eval| eval
                        .heap()
                        .alloc(Tuple::new(xs.try_map(|x| x(eval))?)))
                }
            }
            Expr::List(exprs) => {
                let xs = exprs.into_map(|x| self.expr(x));
                if xs.is_empty() {
                    expr!("list_empty", |eval| eval.heap().alloc(List::default()))
                } else if xs.iter().all(|x| x.as_value().is_some()) {
                    let content = xs.map(|v| v.as_value().unwrap());
                    expr!("list_static", |eval| {
                        let content = coerce_ref(&content).clone();
                        eval.heap().alloc(List::new(content))
                    })
                } else {
                    let xs = xs.into_map(|x| x.as_compiled());
                    expr!("list", |eval| eval
                        .heap()
                        .alloc(List::new(xs.try_map(|x| x(eval))?)))
                }
            }
            Expr::Dict(exprs) => {
                let xs = exprs.into_map(|(k, v)| (self.expr(k), self.expr(v)));
                if xs.is_empty() {
                    return expr!("dict_empty", |eval| eval.heap().alloc(Dict::default()));
                }
                if xs.iter().all(|(k, _)| k.as_value().is_some()) {
                    if xs.iter().all(|(_, v)| v.as_value().is_some()) {
                        let mut res = SmallMap::new();
                        for (k, v) in xs.iter() {
                            res.insert_hashed(
                                k.as_value()
                                    .unwrap()
                                    .get_hashed()
                                    .expect("Dictionary literals are hashable"),
                                v.as_value().unwrap(),
                            );
                        }
                        // If we lost some elements, then there are duplicates, so don't take the fast-literal
                        // path and go down the slow runtime path (which will raise the error).
                        // We have a lint that will likely fire on this issue (and others).
                        if res.len() == xs.len() {
                            return expr!("dict_static", |eval| {
                                let res = coerce_ref(&res).clone();
                                eval.heap().alloc(Dict::new(res))
                            });
                        }
                    } else {
                        // The keys are all constant, but the variables change.
                        // At least we can pre-hash these values.
                        let xs = xs.into_map(|(k, v)| {
                            (
                                k.as_value()
                                    .unwrap()
                                    .get_hashed()
                                    .expect("Dictionary literals are hashable"),
                                v.as_compiled(),
                            )
                        });
                        return expr!("dict_static_key", |eval| {
                            let mut r = SmallMap::with_capacity(xs.len());
                            for (k, v) in &xs {
                                if r.insert_hashed(k.to_hashed_value(), v(eval)?).is_some() {
                                    throw(
                                        Err(EvalError::DuplicateDictionaryKey(k.key().to_string())
                                            .into()),
                                        span,
                                        eval,
                                    )?;
                                }
                            }
                            eval.heap().alloc(Dict::new(r))
                        });
                    }
                }

                let xs = xs.into_map(|(k, v)| (k.as_compiled(), v.as_compiled()));
                expr!("dict", |eval| {
                    let mut r = SmallMap::with_capacity(xs.len());
                    for (k, v) in &xs {
                        let k = k(eval)?;
                        if r.insert_hashed(k.get_hashed()?, v(eval)?).is_some() {
                            throw(
                                Err(EvalError::DuplicateDictionaryKey(k.to_string()).into()),
                                span,
                                eval,
                            )?;
                        }
                    }
                    eval.heap().alloc(Dict::new(r))
                })
            }
            Expr::If(box (cond, then_expr, else_expr)) => {
                let then_expr = self.expr(then_expr);
                let else_expr = self.expr(else_expr);
                let (cond, t, f) = match self.conditional(cond) {
                    Conditional::True => return then_expr,
                    Conditional::False => return else_expr,
                    Conditional::Normal(cond) => (cond, then_expr, else_expr),
                    Conditional::Negate(cond) => (cond, else_expr, then_expr),
                };
                let t = t.as_compiled();
                let f = f.as_compiled();
                expr!("if_expr", |eval| {
                    if cond(eval)?.to_bool() {
                        t(eval)?
                    } else {
                        f(eval)?
                    }
                })
            }
            Expr::Dot(left, right) => {
                let left = self.expr(*left);
                let s = Symbol::new(&right.node);
                expr!("dot", left, |eval| {
                    let (attr_type, v) = throw(get_attr_hashed(left, &s, eval.heap()), span, eval)?;
                    if attr_type == AttrType::Field {
                        v
                    } else if let Some(v_attr) = v.downcast_ref::<NativeAttribute>() {
                        throw(v_attr.call(left, eval), span, eval)?
                    } else {
                        // Insert self so the method see the object it is acting on
                        eval.heap().alloc(BoundMethod::new(left, v))
                    }
                })
            }
            Expr::Call(left, mut args) => {
                match left.node {
                    Expr::Dot(box e, s) => {
                        let e = self.expr(e);
                        let s = Symbol::new(&s.node);
                        let args = self.args(args);
                        args!(
                            args,
                            expr!("call_method", e, |eval| {
                                // We don't need to worry about whether it's an attribute, method or field
                                // since those that don't want the `this` just ignore it
                                let fun = throw(get_attr_hashed(e, &s, eval.heap()), span, eval)?.1;
                                args.with_params(Some(e), eval, |params, eval| {
                                    throw(fun.invoke(Some(span), params, eval), span, eval)
                                })?
                            })
                        )
                    }
                    _ => {
                        let left = self.expr(*left);
                        let one_positional = args.len() == 1 && args[0].is_positional();
                        if left.as_value() == Some(self.constants.fn_type) && one_positional {
                            let x = self.expr(args.pop().unwrap().node.into_expr());
                            expr!("type", x, |_eval| {
                                x.get_ref().get_type_value().to_value()
                            })
                        } else if left.as_value() == Some(self.constants.fn_len) && one_positional {
                            let x = self.expr(args.pop().unwrap().node.into_expr());
                            // Technically the length command _could_ call other functions,
                            // and we'd not get entries on the call stack, which would be bad.
                            // But `len()` is super common, and no one expects it to call other functions,
                            // so let's just ignore that corner case for additional perf.
                            expr!("len", x, |_eval| Value::new_int(x.length()?))
                        } else {
                            let args = self.args(args);
                            args!(
                                args,
                                expr!("call", left, |eval| {
                                    args.with_params(None, eval, |params, eval| {
                                        throw(left.invoke(Some(span), params, eval), span, eval)
                                    })?
                                })
                            )
                        }
                    }
                }
            }
            Expr::ArrayIndirection(box (array, index)) => {
                let array = self.expr(array);
                let index = self.expr(index);
                expr!("index", array, index, |eval| {
                    throw(array.at(index, eval.heap()), span, eval)?
                })
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
                match expr.as_value() {
                    Some(x) => {
                        value!(FrozenValue::new_bool(!x.get_ref().to_bool()))
                    }
                    _ => expr!("not", expr, |_eval| Value::new_bool(!expr.to_bool())),
                }
            }
            Expr::Minus(expr) => {
                let expr = self.expr(*expr);
                match expr
                    .as_value()
                    .and_then(FrozenValue::unpack_int)
                    .and_then(i32::checked_neg)
                {
                    Some(i) => value!(FrozenValue::new_int(i)),
                    _ => expr!("minus", expr, |eval| throw(
                        expr.minus(eval.heap()),
                        span,
                        eval
                    )?),
                }
            }
            Expr::Plus(expr) => {
                let expr = self.expr(*expr);
                match expr.as_value() {
                    Some(x) if x.unpack_int().is_some() => value!(x),
                    _ => expr!("plus", expr, |eval| throw(
                        expr.plus(eval.heap()),
                        span,
                        eval
                    )?),
                }
            }
            Expr::BitNot(expr) => {
                let expr = self.expr(*expr);
                expr!("bit_not", expr, |_eval| Value::new_int(!expr.to_int()?))
            }
            Expr::Op(left, op, right) => {
                if let Some(x) = Expr::reduces_to_string(op, &left, &right) {
                    let val = self.heap.alloc(x);
                    value!(val)
                } else {
                    let l = self.expr(*left);
                    let r = self.expr(*right);
                    match op {
                        BinOp::Or => {
                            let r = r.as_compiled();
                            expr!("or", l, |eval| {
                                if l.to_bool() { l } else { r(eval)? }
                            })
                        }
                        BinOp::And => {
                            let r = r.as_compiled();
                            expr!("and", l, |eval| {
                                if !l.to_bool() { l } else { r(eval)? }
                            })
                        }
                        BinOp::Equal => eval_equals(span, l, r, |x| x),
                        BinOp::NotEqual => eval_equals(span, l, r, |x| !x),
                        BinOp::Less => eval_compare(span, l, r, |x| x == Ordering::Less),
                        BinOp::Greater => eval_compare(span, l, r, |x| x == Ordering::Greater),
                        BinOp::LessOrEqual => eval_compare(span, l, r, |x| x != Ordering::Greater),
                        BinOp::GreaterOrEqual => eval_compare(span, l, r, |x| x != Ordering::Less),
                        BinOp::In => expr!("in", r, l, |eval| {
                            throw(r.is_in(l).map(Value::new_bool), span, eval)?
                        }),
                        BinOp::NotIn => expr!("not_in", r, l, |eval| {
                            throw(r.is_in(l).map(|x| Value::new_bool(!x)), span, eval)?
                        }),
                        BinOp::Subtract => {
                            expr!("subtract", l, r, |eval| throw(
                                l.sub(r, eval.heap()),
                                span,
                                eval
                            )?)
                        }
                        BinOp::Add => expr!("add", l, r, |eval| {
                            // Addition of string is super common and pretty cheap, so have a special case for it.
                            if let Some(ls) = l.unpack_str() {
                                if let Some(rs) = r.unpack_str() {
                                    if ls.is_empty() {
                                        return Ok(r);
                                    } else if rs.is_empty() {
                                        return Ok(l);
                                    } else {
                                        return Ok(eval.heap().alloc_str_concat(ls, rs));
                                    }
                                }
                            }

                            // Written using Value::add so that Rust Analyzer doesn't think it is an error.
                            throw(Value::add(l, r, eval.heap()), span, eval)?
                        }),
                        BinOp::Multiply => {
                            expr!("multiply", l, r, |eval| throw(
                                l.mul(r, eval.heap()),
                                span,
                                eval
                            )?)
                        }
                        BinOp::Percent => expr!("percent", l, r, |eval| {
                            throw(l.percent(r, eval.heap()), span, eval)?
                        }),
                        BinOp::FloorDivide => expr!("floor_divide", l, r, |eval| {
                            throw(l.floor_div(r, eval.heap()), span, eval)?
                        }),
                        BinOp::BitAnd => {
                            expr!("bit_and", l, r, |eval| throw(l.bit_and(r), span, eval)?)
                        }
                        BinOp::BitOr => {
                            expr!("bit_or", l, r, |eval| throw(l.bit_or(r), span, eval)?)
                        }
                        BinOp::BitXor => {
                            expr!("bit_xor", l, r, |eval| throw(l.bit_xor(r), span, eval)?)
                        }
                        BinOp::LeftShift => {
                            expr!("left_shift", l, r, |eval| throw(
                                l.left_shift(r),
                                span,
                                eval
                            )?)
                        }
                        BinOp::RightShift => {
                            expr!("right_shift", l, r, |eval| throw(
                                l.right_shift(r),
                                span,
                                eval
                            )?)
                        }
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
                value!(val)
            }
        }
    }
}
