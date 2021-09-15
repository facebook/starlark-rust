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
    errors::did_you_mean::did_you_mean,
    eval::{
        compiler::{
            expr_throw,
            scope::{AssignCount, Captured, CstExpr, ResolvedIdent, Slot},
            Compiler, ExprEvalException,
        },
        fragment::known::{list_to_tuple, Conditional},
        runtime::{evaluator::Evaluator, slots::LocalSlotId},
    },
    syntax::ast::{AstExprP, AstLiteral, AstPayload, AstString, BinOp, ExprP, StmtP},
    values::{
        dict::Dict,
        function::{BoundMethod, NativeAttribute},
        list::List,
        tuple::{FrozenTuple, Tuple},
        AttrType, FrozenHeap, FrozenStringValue, FrozenValue, Heap, Value, ValueError, ValueLike,
    },
};
use gazebo::{coerce::coerce_ref, prelude::*};
use std::cmp::Ordering;
use thiserror::Error;

/// `bool` operation.
#[derive(Copy, Clone, Dupe)]
pub(crate) enum MaybeNot {
    Id,
    Not,
}

impl MaybeNot {
    fn as_fn(self) -> fn(bool) -> bool {
        match self {
            MaybeNot::Id => |x| x,
            MaybeNot::Not => |x| !x,
        }
    }
}

pub(crate) type ExprCompiled = Box<
    dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Value<'v>, ExprEvalException> + Send + Sync,
>;
pub(crate) enum ExprCompiledValue {
    Value(FrozenValue),
    Compiled(ExprCompiled),
    /// Read local non-captured variable.
    Local(LocalSlotId, Spanned<String>),
    /// `type(x)`
    Type(Box<ExprCompiledValue>),
    /// `maybe_not(type(x) == "y")`
    TypeIs(Box<ExprCompiledValue>, FrozenStringValue, MaybeNot),
}

impl ExprCompiledValue {
    pub fn as_value(&self) -> Option<FrozenValue> {
        match self {
            Self::Value(x) => Some(*x),
            _ => None,
        }
    }

    pub fn as_compiled(self) -> ExprCompiled {
        match self {
            Self::Value(x) => box move |_| Ok(x.to_value()),
            Self::Compiled(x) => x,
            Self::Local(slot, name) => expr!("local", |eval| expr_throw(
                eval.get_slot_local(slot, &name.node),
                name.span,
                eval
            )?)
            .as_compiled(),
            Self::Type(x) => expr!("type", x, |_eval| {
                x.get_ref().get_type_value().unpack().to_value()
            })
            .as_compiled(),
            ExprCompiledValue::TypeIs(e, t, maybe_not) => {
                let cmp = maybe_not.as_fn();
                expr!("type_is", e, |_eval| {
                    Value::new_bool(cmp(e.get_type_value() == t))
                })
                .as_compiled()
            }
        }
    }
}

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
    if let (Some(l), Some(r)) = (l.as_value(), r.as_value()) {
        // If comparison fails, let it fail in runtime.
        if let Ok(r) = l.compare(r.to_value()) {
            return value!(FrozenValue::new_bool(cmp(r)));
        }
    }

    expr!("compare", l, r, |eval| {
        Value::new_bool(cmp(expr_throw(l.compare(r), span, eval)?))
    })
}

/// Try fold expression `cmp(l == r)` into `cmp(type(x) == "y")`.
/// Return original `l` and `r` arguments if fold was unsuccessful.
fn try_eval_type_is(
    l: ExprCompiledValue,
    r: ExprCompiledValue,
    maybe_not: MaybeNot,
) -> Result<ExprCompiledValue, (ExprCompiledValue, ExprCompiledValue)> {
    match (l, r) {
        (ExprCompiledValue::Type(l), ExprCompiledValue::Value(r)) => {
            if let Some(r) = FrozenStringValue::new(r) {
                Ok(ExprCompiledValue::TypeIs(l, r, maybe_not))
            } else {
                Err((ExprCompiledValue::Type(l), ExprCompiledValue::Value(r)))
            }
        }
        (l, r) => Err((l, r)),
    }
}

fn eval_equals(
    span: Span,
    l: ExprCompiledValue,
    r: ExprCompiledValue,
    maybe_not: MaybeNot,
) -> ExprCompiledValue {
    let cmp = maybe_not.as_fn();
    if let (Some(l), Some(r)) = (l.as_value(), r.as_value()) {
        // If comparison fails, let it fail in runtime.
        if let Ok(r) = l.equals(r.to_value()) {
            return value!(FrozenValue::new_bool(cmp(r)));
        }
    }

    let (l, r) = match try_eval_type_is(l, r, maybe_not) {
        Ok(e) => return e,
        Err((l, r)) => (l, r),
    };

    let (r, l) = match try_eval_type_is(r, l, maybe_not) {
        Ok(e) => return e,
        Err((r, l)) => (r, l),
    };

    expr!("equals", l, r, |eval| {
        Value::new_bool(cmp(expr_throw(l.equals(r), span, eval)?))
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
        expr_throw(
            collection.slice(start, stop, stride, eval.heap()),
            span,
            eval,
        )?
    })
}

impl AstLiteral {
    fn compile(&self, heap: &FrozenHeap) -> FrozenValue {
        match self {
            AstLiteral::IntLiteral(i) => FrozenValue::new_int(i.node),
            AstLiteral::StringLiteral(x) => heap.alloc(x.node.as_str()),
        }
    }
}

impl<P: AstPayload> ExprP<P> {
    fn unpack_string_literal(&self) -> Option<&str> {
        match self {
            ExprP::Literal(AstLiteral::StringLiteral(i)) => Some(&i.node),
            _ => None,
        }
    }

    // Does an entire sequence of additions reduce to a string literal
    fn reduces_to_string<'a>(
        mut op: BinOp,
        mut left: &'a AstExprP<P>,
        mut right: &'a AstExprP<P>,
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
                ExprP::Op(left2, op2, right2) => {
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
}

#[cold]
#[inline(never)]
fn get_attr_no_attr_error<'v>(x: Value<'v>, attribute: &Symbol) -> anyhow::Error {
    match did_you_mean(attribute.as_str(), x.dir_attr().iter().map(|s| s.as_str())) {
        None => ValueError::NoAttr(x.get_type().to_owned(), attribute.as_str().to_owned()).into(),
        Some(better) => ValueError::NoAttrDidYouMean(
            x.get_type().to_owned(),
            attribute.as_str().to_owned(),
            better.to_owned(),
        )
        .into(),
    }
}

pub(crate) fn get_attr_hashed<'v>(
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
        None => Err(get_attr_no_attr_error(x, attribute)),
        Some(x) => Ok((AttrType::Field, x)),
    }
}

impl Compiler<'_> {
    pub fn expr_opt(&mut self, expr: Option<Box<CstExpr>>) -> Option<ExprCompiledValue> {
        expr.map(|v| self.expr(*v))
    }

    pub(crate) fn compile_time_getattr(
        &mut self,
        left: FrozenValue,
        attr: &Symbol,
    ) -> Option<(AttrType, FrozenValue)> {
        // We assume `getattr` has no side effects.
        let (attr_type, field) =
            get_attr_hashed(left.to_value(), attr, self.module_env.heap()).ok()?;
        // We take only frozen values, so if getattr returns fresh object on each call,
        // we are discarding the result.
        let field = field.unpack_frozen()?;
        Some((attr_type, field))
    }

    fn expr_ident(
        &mut self,
        ident: AstString,
        resolved_ident: Option<ResolvedIdent>,
    ) -> ExprCompiledValue {
        let resolved_ident =
            resolved_ident.unwrap_or_else(|| panic!("variable not resolved: `{}`", ident.node));
        let name = ident.node;
        let span = ident.span;
        match resolved_ident {
            ResolvedIdent::Slot((Slot::Local(slot), binding_id)) => {
                let binding = self.scope_data.get_binding(binding_id);

                // We can't look up the local variabless in advance, because they are different each time
                // we go through a new function call.
                match binding.captured {
                    Captured::Yes => expr!("local_captured", |eval| expr_throw(
                        eval.get_slot_local_captured(slot, &name),
                        span,
                        eval
                    )?),
                    Captured::No => ExprCompiledValue::Local(slot, Spanned { node: name, span }),
                }
            }
            ResolvedIdent::Slot((Slot::Module(slot), binding_id)) => {
                let binding = self.scope_data.get_binding(binding_id);

                // We can only inline variables if they were assigned once
                // otherwise we might inline the wrong value.
                if binding.assign_count == AssignCount::AtMostOnce {
                    if let Some(v) = self.module_env.slots().get_slot(slot) {
                        // We could inline non-frozen values, but these values
                        // can be garbage-collected, so it is somewhat harder to implement.
                        if let Some(v) = v.unpack_frozen() {
                            return value!(v);
                        }
                    }
                }
                // We can't look up the module variables in advance because the first time around they are
                // mutables, but after freezing they point at a different set of frozen slots.
                expr!("module", |eval| expr_throw(
                    eval.get_slot_module(slot),
                    span,
                    eval
                )?)
            }
            ResolvedIdent::Global(v) => value!(v),
        }
    }

    pub(crate) fn expr_spanned(&mut self, expr: CstExpr) -> Spanned<ExprCompiledValue> {
        Spanned {
            span: expr.span,
            node: self.expr(expr),
        }
    }

    pub fn expr(&mut self, expr: CstExpr) -> ExprCompiledValue {
        // println!("compile {}", expr.node);
        let span = expr.span;
        match expr.node {
            ExprP::Identifier(ident, resolved_ident) => self.expr_ident(ident, resolved_ident),
            ExprP::Lambda(params, box inner, scope_id) => {
                let suite = Spanned {
                    span: expr.span,
                    node: StmtP::Return(Some(inner)),
                };
                self.function("lambda", scope_id, params, None, suite)
            }
            ExprP::Tuple(exprs) => {
                let xs = exprs.into_map(|x| self.expr(x));
                if xs.iter().all(|x| x.as_value().is_some()) {
                    let content = xs.map(|v| v.as_value().unwrap());
                    let result = self.module_env.frozen_heap().alloc(FrozenTuple { content });
                    value!(result)
                } else {
                    let xs = xs.into_map(|x| x.as_compiled());
                    expr!("tuple", |eval| eval
                        .heap()
                        .alloc(Tuple::new(xs.try_map(|x| x(eval))?)))
                }
            }
            ExprP::List(exprs) => {
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
            ExprP::Dict(exprs) => {
                let xs = exprs.into_map(|(k, v)| (self.expr_spanned(k), self.expr(v)));
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
                                    expr_throw(
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

                let xs = xs.into_map(|(k, v)| {
                    (
                        Spanned {
                            span: k.span,
                            node: k.node.as_compiled(),
                        },
                        v.as_compiled(),
                    )
                });
                expr!("dict", |eval| {
                    let mut r = SmallMap::with_capacity(xs.len());
                    for (k, v) in &xs {
                        let k_value = k(eval)?;
                        if r.insert_hashed(
                            expr_throw(k_value.get_hashed(), k.span, eval)?,
                            v(eval)?,
                        )
                        .is_some()
                        {
                            expr_throw(
                                Err(EvalError::DuplicateDictionaryKey(k_value.to_string()).into()),
                                span,
                                eval,
                            )?;
                        }
                    }
                    eval.heap().alloc(Dict::new(r))
                })
            }
            ExprP::If(box (cond, then_expr, else_expr)) => {
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
            ExprP::Dot(left, right) => {
                let left = self.expr(*left);
                let s = Symbol::new(&right.node);

                if let Some(left) = left.as_value() {
                    if let Some((attr_type, v)) = self.compile_time_getattr(left, &s) {
                        if attr_type == AttrType::Field {
                            return ExprCompiledValue::Value(v);
                        } else {
                            // TODO: maybe call attribute at compile time
                            // TODO: maybe create bound method at compile time
                        }
                    }
                }

                expr!("dot", left, |eval| {
                    let (attr_type, v) =
                        expr_throw(get_attr_hashed(left, &s, eval.heap()), span, eval)?;
                    if attr_type == AttrType::Field {
                        v
                    } else if let Some(v_attr) = v.downcast_ref::<NativeAttribute>() {
                        expr_throw(v_attr.call(left, eval), span, eval)?
                    } else {
                        // Insert self so the method see the object it is acting on
                        eval.heap().alloc(BoundMethod::new(left, v))
                    }
                })
            }
            ExprP::Call(box left, args) => self.expr_call(span, left, args),
            ExprP::ArrayIndirection(box (array, index)) => {
                let array = self.expr(array);
                let index = self.expr(index);
                expr!("index", array, index, |eval| {
                    expr_throw(array.at(index, eval.heap()), span, eval)?
                })
            }
            ExprP::Slice(collection, start, stop, stride) => {
                let collection = self.expr(*collection);
                let start = start.map(|x| self.expr(*x));
                let stop = stop.map(|x| self.expr(*x));
                let stride = stride.map(|x| self.expr(*x));
                eval_slice(span, collection, start, stop, stride)
            }
            ExprP::Not(expr) => {
                let expr = self.expr(*expr);
                match expr.as_value() {
                    Some(x) => {
                        value!(FrozenValue::new_bool(!x.get_ref().to_bool()))
                    }
                    _ => expr!("not", expr, |_eval| Value::new_bool(!expr.to_bool())),
                }
            }
            ExprP::Minus(expr) => {
                let expr = self.expr(*expr);
                match expr
                    .as_value()
                    .and_then(FrozenValue::unpack_int)
                    .and_then(i32::checked_neg)
                {
                    Some(i) => value!(FrozenValue::new_int(i)),
                    _ => expr!("minus", expr, |eval| expr_throw(
                        expr.minus(eval.heap()),
                        span,
                        eval
                    )?),
                }
            }
            ExprP::Plus(expr) => {
                let expr = self.expr(*expr);
                match expr.as_value() {
                    Some(x) if x.unpack_int().is_some() => value!(x),
                    _ => expr!("plus", expr, |eval| expr_throw(
                        expr.plus(eval.heap()),
                        span,
                        eval
                    )?),
                }
            }
            ExprP::BitNot(expr) => {
                let expr = self.expr(*expr);
                expr!("bit_not", expr, |eval| Value::new_int(!expr_throw(
                    expr.to_int(),
                    span,
                    eval
                )?))
            }
            ExprP::Op(left, op, right) => {
                if let Some(x) = ExprP::reduces_to_string(op, &left, &right) {
                    let val = self.module_env.frozen_heap().alloc(x);
                    value!(val)
                } else {
                    let right = if op == BinOp::In || op == BinOp::NotIn {
                        list_to_tuple(*right)
                    } else {
                        *right
                    };

                    let l = self.expr(*left);
                    let r = self.expr(right);
                    match op {
                        BinOp::Or => {
                            if let Some(l) = l.as_value() {
                                if l.to_value().to_bool() { value!(l) } else { r }
                            } else {
                                let r = r.as_compiled();
                                expr!("or", l, |eval| {
                                    if l.to_bool() { l } else { r(eval)? }
                                })
                            }
                        }
                        BinOp::And => {
                            if let Some(l) = l.as_value() {
                                if !l.to_value().to_bool() {
                                    value!(l)
                                } else {
                                    r
                                }
                            } else {
                                let r = r.as_compiled();
                                expr!("and", l, |eval| {
                                    if !l.to_bool() { l } else { r(eval)? }
                                })
                            }
                        }
                        BinOp::Equal => eval_equals(span, l, r, MaybeNot::Id),
                        BinOp::NotEqual => eval_equals(span, l, r, MaybeNot::Not),
                        BinOp::Less => eval_compare(span, l, r, |x| x == Ordering::Less),
                        BinOp::Greater => eval_compare(span, l, r, |x| x == Ordering::Greater),
                        BinOp::LessOrEqual => eval_compare(span, l, r, |x| x != Ordering::Greater),
                        BinOp::GreaterOrEqual => eval_compare(span, l, r, |x| x != Ordering::Less),
                        BinOp::In => expr!("in", r, l, |eval| {
                            expr_throw(r.is_in(l).map(Value::new_bool), span, eval)?
                        }),
                        BinOp::NotIn => expr!("not_in", r, l, |eval| {
                            expr_throw(r.is_in(l).map(|x| Value::new_bool(!x)), span, eval)?
                        }),
                        BinOp::Subtract => {
                            expr!("subtract", l, r, |eval| expr_throw(
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
                            expr_throw(Value::add(l, r, eval.heap()), span, eval)?
                        }),
                        BinOp::Multiply => {
                            expr!("multiply", l, r, |eval| expr_throw(
                                l.mul(r, eval.heap()),
                                span,
                                eval
                            )?)
                        }
                        BinOp::Percent => expr!("percent", l, r, |eval| {
                            expr_throw(l.percent(r, eval.heap()), span, eval)?
                        }),
                        BinOp::FloorDivide => expr!("floor_divide", l, r, |eval| {
                            expr_throw(l.floor_div(r, eval.heap()), span, eval)?
                        }),
                        BinOp::BitAnd => {
                            expr!("bit_and", l, r, |eval| expr_throw(
                                l.bit_and(r),
                                span,
                                eval
                            )?)
                        }
                        BinOp::BitOr => {
                            expr!("bit_or", l, r, |eval| expr_throw(l.bit_or(r), span, eval)?)
                        }
                        BinOp::BitXor => {
                            expr!("bit_xor", l, r, |eval| expr_throw(
                                l.bit_xor(r),
                                span,
                                eval
                            )?)
                        }
                        BinOp::LeftShift => {
                            expr!("left_shift", l, r, |eval| expr_throw(
                                l.left_shift(r),
                                span,
                                eval
                            )?)
                        }
                        BinOp::RightShift => {
                            expr!("right_shift", l, r, |eval| expr_throw(
                                l.right_shift(r),
                                span,
                                eval
                            )?)
                        }
                    }
                }
            }
            ExprP::ListComprehension(x, box for_, clauses) => {
                self.list_comprehension(*x, for_, clauses)
            }
            ExprP::DictComprehension(box (k, v), box for_, clauses) => {
                self.dict_comprehension(k, v, for_, clauses)
            }
            ExprP::Literal(x) => {
                let val = x.compile(self.module_env.frozen_heap());
                value!(val)
            }
        }
    }
}
