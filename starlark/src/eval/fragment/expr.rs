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
use std::cmp::Ordering;

use gazebo::prelude::*;
use thiserror::Error;

use crate::{
    codemap::{Span, Spanned},
    collections::symbol_map::Symbol,
    environment::{slots::ModuleSlotId, FrozenModuleRef},
    errors::did_you_mean::did_you_mean,
    eval::{
        compiler::{
            scope::{AssignCount, Captured, CstExpr, ResolvedIdent, Slot},
            Compiler,
        },
        fragment::{
            call::CallCompiled, compr::ComprCompiled, def::DefCompiled, known::list_to_tuple,
        },
        runtime::slots::LocalSlotId,
    },
    syntax::ast::{AstExprP, AstLiteral, AstPayload, AstString, BinOp, ExprP, StmtP},
    values::{
        string::interpolation::parse_percent_s_one, AttrType, FrozenHeap, FrozenStringValue,
        FrozenValue, Heap, Value, ValueError, ValueLike,
    },
};

/// `bool` operation.
#[derive(Copy, Clone, Dupe, Eq, PartialEq, Debug)]
pub(crate) enum MaybeNot {
    Id,
    Not,
}

impl MaybeNot {
    pub(crate) fn negate(self) -> MaybeNot {
        match self {
            MaybeNot::Id => MaybeNot::Not,
            MaybeNot::Not => MaybeNot::Id,
        }
    }

    fn as_fn(self) -> fn(bool) -> bool {
        match self {
            MaybeNot::Id => |x| x,
            MaybeNot::Not => |x| !x,
        }
    }
}

/// Map result of comparison to boolean.
#[derive(Copy, Clone, Dupe, Debug)]
pub(crate) enum CompareOp {
    Less,
    Greater,
    LessOrEqual,
    GreaterOrEqual,
}

impl CompareOp {
    fn as_fn(self) -> fn(Ordering) -> bool {
        match self {
            CompareOp::Less => |x| x == Ordering::Less,
            CompareOp::Greater => |x| x == Ordering::Greater,
            CompareOp::LessOrEqual => |x| x != Ordering::Greater,
            CompareOp::GreaterOrEqual => |x| x != Ordering::Less,
        }
    }
}

#[derive(Copy, Clone, Dupe, Debug)]
pub(crate) enum ExprBinOp {
    In,
    NotIn,
    Sub,
    Add,
    Multiply,
    Percent,
    Divide,
    FloorDivide,
    BitAnd,
    BitOr,
    BitXor,
    LeftShift,
    RightShift,
}

#[derive(Clone, Debug)]
pub(crate) enum ExprCompiledValue {
    Value(FrozenValue),
    /// Read local non-captured variable.
    Local(LocalSlotId),
    /// Read local captured variable.
    LocalCaptured(LocalSlotId),
    Module(ModuleSlotId),
    /// `cmp(x <=> y)`
    Equals(
        Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>,
        MaybeNot,
    ),
    /// `cmp(x <=> y)`
    Compare(
        Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>,
        CompareOp,
    ),
    /// `type(x)`
    Type(Box<Spanned<ExprCompiledValue>>),
    /// `len(x)`
    Len(Box<Spanned<ExprCompiledValue>>),
    /// `maybe_not(type(x) == "y")`
    TypeIs(Box<Spanned<ExprCompiledValue>>, FrozenStringValue, MaybeNot),
    Tuple(Vec<Spanned<ExprCompiledValue>>),
    List(Vec<Spanned<ExprCompiledValue>>),
    Dict(Vec<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>),
    /// Comprehension.
    Compr(ComprCompiled),
    Dot(Box<Spanned<ExprCompiledValue>>, Symbol),
    ArrayIndirection(Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>),
    If(
        Box<(
            Spanned<ExprCompiledValue>,
            Spanned<ExprCompiledValue>,
            Spanned<ExprCompiledValue>,
        )>,
    ),
    Slice(
        Box<(
            Spanned<ExprCompiledValue>,
            Option<Spanned<ExprCompiledValue>>,
            Option<Spanned<ExprCompiledValue>>,
            Option<Spanned<ExprCompiledValue>>,
        )>,
    ),
    Not(Box<Spanned<ExprCompiledValue>>),
    Minus(Box<Spanned<ExprCompiledValue>>),
    Plus(Box<Spanned<ExprCompiledValue>>),
    BitNot(Box<Spanned<ExprCompiledValue>>),
    And(Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>),
    Or(Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>),
    Op(
        ExprBinOp,
        Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>,
    ),
    /// `"aaa%sbbb" % arg`
    PercentSOne(
        Box<(
            FrozenStringValue,
            Spanned<ExprCompiledValue>,
            FrozenStringValue,
        )>,
    ),
    /// `"aaa%sbbb".format(arg)`
    FormatOne(
        Box<(
            FrozenStringValue,
            Spanned<ExprCompiledValue>,
            FrozenStringValue,
        )>,
    ),
    Call(Spanned<CallCompiled>),
    Def(DefCompiled),
}

impl ExprCompiledValue {
    pub fn as_value(&self) -> Option<FrozenValue> {
        match self {
            Self::Value(x) => Some(*x),
            _ => None,
        }
    }

    /// Is expression a constant string?
    pub(crate) fn as_string(&self) -> Option<FrozenStringValue> {
        FrozenStringValue::new(self.as_value()?)
    }
}

impl Spanned<ExprCompiledValue> {
    pub(crate) fn optimize_on_freeze(
        &self,
        module: &FrozenModuleRef,
    ) -> Spanned<ExprCompiledValue> {
        let span = self.span;
        let expr = match self.node {
            ref e @ (ExprCompiledValue::Value(..)
            | ExprCompiledValue::Local(..)
            | ExprCompiledValue::LocalCaptured(..)) => e.clone(),
            ExprCompiledValue::Module(slot) => {
                match module.get_module_data().get_slot(slot) {
                    None => {
                        // Let if fail at runtime.
                        ExprCompiledValue::Module(slot)
                    }
                    Some(v) => ExprCompiledValue::Value(v),
                }
            }
            ExprCompiledValue::Equals(box (ref l, ref r), maybe_not) => {
                let l = l.optimize_on_freeze(module);
                let r = r.optimize_on_freeze(module);
                eval_equals(l, r, maybe_not)
            }
            ExprCompiledValue::Compare(box (ref l, ref r), cmp) => {
                let l = l.optimize_on_freeze(module);
                let r = r.optimize_on_freeze(module);
                ExprCompiledValue::Compare(box (l, r), cmp)
            }
            ExprCompiledValue::Type(box ref e) => {
                ExprCompiledValue::Type(box e.optimize_on_freeze(module))
            }
            ExprCompiledValue::Len(box ref e) => {
                ExprCompiledValue::Len(box e.optimize_on_freeze(module))
            }
            ExprCompiledValue::TypeIs(box ref e, t, maybe_not) => {
                ExprCompiledValue::TypeIs(box e.optimize_on_freeze(module), t, maybe_not)
            }
            ExprCompiledValue::Tuple(ref xs) => {
                ExprCompiledValue::Tuple(xs.map(|e| e.optimize_on_freeze(module)))
            }
            ExprCompiledValue::List(ref xs) => {
                ExprCompiledValue::List(xs.map(|e| e.optimize_on_freeze(module)))
            }
            ExprCompiledValue::Dict(ref kvs) => ExprCompiledValue::Dict(
                kvs.map(|(k, v)| (k.optimize_on_freeze(module), v.optimize_on_freeze(module))),
            ),
            ExprCompiledValue::Compr(ref compr) => compr.optimize_on_freeze(module),
            ExprCompiledValue::Dot(box ref object, ref field) => {
                ExprCompiledValue::Dot(box object.optimize_on_freeze(module), field.clone())
            }
            ExprCompiledValue::ArrayIndirection(box (ref array, ref index)) => {
                let array = array.optimize_on_freeze(module);
                let index = index.optimize_on_freeze(module);
                ExprCompiledValue::ArrayIndirection(box (array, index))
            }
            ExprCompiledValue::If(box (ref cond, ref t, ref f)) => {
                let cond = cond.optimize_on_freeze(module);
                let t = t.optimize_on_freeze(module);
                let f = f.optimize_on_freeze(module);
                return ExprCompiledValue::if_expr(cond, t, f);
            }
            ExprCompiledValue::Slice(box (ref v, ref start, ref stop, ref step)) => {
                let v = v.optimize_on_freeze(module);
                let start = start.as_ref().map(|x| x.optimize_on_freeze(module));
                let stop = stop.as_ref().map(|x| x.optimize_on_freeze(module));
                let step = step.as_ref().map(|x| x.optimize_on_freeze(module));
                ExprCompiledValue::Slice(box (v, start, stop, step))
            }
            ExprCompiledValue::Not(box ref e) => {
                let e = e.optimize_on_freeze(module);
                return ExprCompiledValue::not(span, e);
            }
            ExprCompiledValue::Minus(box ref e) => {
                let e = e.optimize_on_freeze(module);
                ExprCompiledValue::minus(e)
            }
            ExprCompiledValue::Plus(box ref e) => {
                ExprCompiledValue::Plus(box e.optimize_on_freeze(module))
            }
            ExprCompiledValue::BitNot(box ref e) => {
                ExprCompiledValue::BitNot(box e.optimize_on_freeze(module))
            }
            ExprCompiledValue::And(box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(module);
                let r = r.optimize_on_freeze(module);
                return ExprCompiledValue::and(l, r);
            }
            ExprCompiledValue::Or(box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(module);
                let r = r.optimize_on_freeze(module);
                return ExprCompiledValue::or(l, r);
            }
            ExprCompiledValue::Op(op, box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(module);
                let r = r.optimize_on_freeze(module);
                ExprCompiledValue::Op(op, box (l, r))
            }
            ExprCompiledValue::PercentSOne(box (before, ref arg, after)) => {
                let arg = arg.optimize_on_freeze(module);
                ExprCompiledValue::PercentSOne(box (before, arg, after))
            }
            ExprCompiledValue::FormatOne(box (before, ref arg, after)) => {
                let arg = arg.optimize_on_freeze(module);
                ExprCompiledValue::FormatOne(box (before, arg, after))
            }
            ref d @ ExprCompiledValue::Def(..) => d.clone(),
            ExprCompiledValue::Call(ref call) => call.optimize_on_freeze(module),
        };
        Spanned { node: expr, span }
    }
}

impl ExprCompiledValue {
    fn not(span: Span, expr: Spanned<ExprCompiledValue>) -> Spanned<ExprCompiledValue> {
        match expr {
            Spanned {
                node: ExprCompiledValue::Value(x),
                ..
            } => Spanned {
                node: value!(FrozenValue::new_bool(!x.to_value().to_bool())),
                span,
            },
            expr => Spanned {
                node: ExprCompiledValue::Not(box expr),
                span,
            },
        }
    }

    fn or(
        l: Spanned<ExprCompiledValue>,
        r: Spanned<ExprCompiledValue>,
    ) -> Spanned<ExprCompiledValue> {
        let l_span = l.span;
        if let Some(l) = l.as_value() {
            if l.to_value().to_bool() {
                Spanned {
                    node: value!(l),
                    span: l_span,
                }
            } else {
                r
            }
        } else {
            let span = l.span.merge(r.span);
            Spanned {
                node: ExprCompiledValue::Or(box (l, r)),
                span,
            }
        }
    }

    fn and(
        l: Spanned<ExprCompiledValue>,
        r: Spanned<ExprCompiledValue>,
    ) -> Spanned<ExprCompiledValue> {
        let l_span = l.span;
        if let Some(l) = l.as_value() {
            if !l.to_value().to_bool() {
                Spanned {
                    node: value!(l),
                    span: l_span,
                }
            } else {
                r
            }
        } else {
            let span = l.span.merge(r.span);
            Spanned {
                node: ExprCompiledValue::And(box (l, r)),
                span,
            }
        }
    }

    fn if_expr(
        cond: Spanned<ExprCompiledValue>,
        t: Spanned<ExprCompiledValue>,
        f: Spanned<ExprCompiledValue>,
    ) -> Spanned<ExprCompiledValue> {
        match cond {
            Spanned {
                node: ExprCompiledValue::Value(cond),
                ..
            } => {
                if cond.to_value().to_bool() {
                    t
                } else {
                    f
                }
            }
            Spanned {
                node: ExprCompiledValue::Not(box cond),
                ..
            } => Self::if_expr(cond, f, t),
            cond => {
                let span = cond.span.merge(t.span).merge(f.span);
                Spanned {
                    node: ExprCompiledValue::If(box (cond, t, f)),
                    span,
                }
            }
        }
    }

    fn minus(expr: Spanned<ExprCompiledValue>) -> ExprCompiledValue {
        match expr
            .as_value()
            .and_then(FrozenValue::unpack_int)
            .and_then(i32::checked_neg)
        {
            Some(i) => value!(FrozenValue::new_int(i)),
            _ => ExprCompiledValue::Minus(box expr),
        }
    }
}

#[derive(Debug, Clone, Error)]
pub(crate) enum EvalError {
    #[error("Dictionary key repeated for `{0}`")]
    DuplicateDictionaryKey(String),
}

fn eval_compare(
    l: Spanned<ExprCompiledValue>,
    r: Spanned<ExprCompiledValue>,
    cmp: CompareOp,
) -> ExprCompiledValue {
    if let (Some(l), Some(r)) = (l.as_value(), r.as_value()) {
        // If comparison fails, let it fail in runtime.
        if let Ok(r) = l.compare(r.to_value()) {
            return value!(FrozenValue::new_bool((cmp.as_fn())(r)));
        }
    }

    ExprCompiledValue::Compare(box (l, r), cmp)
}

/// Try fold expression `cmp(l == r)` into `cmp(type(x) == "y")`.
/// Return original `l` and `r` arguments if fold was unsuccessful.
fn try_eval_type_is(
    l: Spanned<ExprCompiledValue>,
    r: Spanned<ExprCompiledValue>,
    maybe_not: MaybeNot,
) -> Result<Spanned<ExprCompiledValue>, (Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)> {
    match (l, r) {
        (
            Spanned {
                node: ExprCompiledValue::Type(l),
                span: l_span,
            },
            Spanned {
                node: ExprCompiledValue::Value(r),
                span: r_span,
            },
        ) => {
            if let Some(r) = FrozenStringValue::new(r) {
                Ok(Spanned {
                    node: ExprCompiledValue::TypeIs(l, r, maybe_not),
                    span: l_span.merge(r_span),
                })
            } else {
                Err((
                    Spanned {
                        node: ExprCompiledValue::Type(l),
                        span: l_span,
                    },
                    Spanned {
                        node: ExprCompiledValue::Value(r),
                        span: r_span,
                    },
                ))
            }
        }
        (l, r) => Err((l, r)),
    }
}

fn eval_equals(
    l: Spanned<ExprCompiledValue>,
    r: Spanned<ExprCompiledValue>,
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
        Ok(e) => return e.node,
        Err((l, r)) => (l, r),
    };

    let (r, l) = match try_eval_type_is(r, l, maybe_not) {
        Ok(e) => return e.node,
        Err((r, l)) => (r, l),
    };

    ExprCompiledValue::Equals(box (l, r), maybe_not)
}

impl AstLiteral {
    fn compile(&self, heap: &FrozenHeap) -> FrozenValue {
        match self {
            AstLiteral::Int(i) => FrozenValue::new_int(i.node),
            AstLiteral::Float(f) => heap.alloc(f.node),
            AstLiteral::String(x) => heap.alloc(x.node.as_str()),
        }
    }
}

impl<P: AstPayload> ExprP<P> {
    fn unpack_string_literal(&self) -> Option<&str> {
        match self {
            ExprP::Literal(AstLiteral::String(i)) => Some(&i.node),
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
    pub fn expr_opt(&mut self, expr: Option<Box<CstExpr>>) -> Option<Spanned<ExprCompiledValue>> {
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
        match resolved_ident {
            ResolvedIdent::Slot((Slot::Local(slot), binding_id)) => {
                let binding = self.scope_data.get_binding(binding_id);

                // We can't look up the local variabless in advance, because they are different each time
                // we go through a new function call.
                match binding.captured {
                    Captured::Yes => ExprCompiledValue::LocalCaptured(slot),
                    Captured::No => ExprCompiledValue::Local(slot),
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

                ExprCompiledValue::Module(slot)
            }
            ResolvedIdent::Global(v) => value!(v),
        }
    }

    fn percent(
        &mut self,
        l: Spanned<ExprCompiledValue>,
        r: Spanned<ExprCompiledValue>,
    ) -> ExprCompiledValue {
        if let Some(v) = l.as_string() {
            if let Some((before, after)) = parse_percent_s_one(&v) {
                let before = self.module_env.frozen_heap().alloc_string_value(&before);
                let after = self.module_env.frozen_heap().alloc_string_value(&after);
                return ExprCompiledValue::PercentSOne(box (before, r, after));
            }
        }
        ExprCompiledValue::Op(ExprBinOp::Percent, box (l, r))
    }

    pub(crate) fn expr(&mut self, expr: CstExpr) -> Spanned<ExprCompiledValue> {
        // println!("compile {}", expr.node);
        let span = expr.span;
        let expr = match expr.node {
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
                    let result = self.module_env.frozen_heap().alloc_tuple(&content);
                    value!(result)
                } else {
                    ExprCompiledValue::Tuple(xs)
                }
            }
            ExprP::List(exprs) => {
                let xs = exprs.into_map(|x| self.expr(x));
                ExprCompiledValue::List(xs)
            }
            ExprP::Dict(exprs) => {
                let xs = exprs.into_map(|(k, v)| (self.expr(k), self.expr(v)));
                ExprCompiledValue::Dict(xs)
            }
            ExprP::If(box (cond, then_expr, else_expr)) => {
                let cond = self.expr(cond);
                let then_expr = self.expr(then_expr);
                let else_expr = self.expr(else_expr);
                return ExprCompiledValue::if_expr(cond, then_expr, else_expr);
            }
            ExprP::Dot(left, right) => {
                let left = self.expr(*left);
                let s = Symbol::new(&right.node);

                if let Some(left) = left.as_value() {
                    if let Some((attr_type, v)) = self.compile_time_getattr(left, &s) {
                        if attr_type == AttrType::Field {
                            return Spanned {
                                span,
                                node: ExprCompiledValue::Value(v),
                            };
                        } else {
                            // TODO: maybe call attribute at compile time
                            // TODO: maybe create bound method at compile time
                        }
                    }
                }

                ExprCompiledValue::Dot(box left, s)
            }
            ExprP::Call(box left, args) => self.expr_call(span, left, args),
            ExprP::ArrayIndirection(box (array, index)) => {
                let array = self.expr(array);
                let index = self.expr(index);
                ExprCompiledValue::ArrayIndirection(box (array, index))
            }
            ExprP::Slice(collection, start, stop, stride) => {
                let collection = self.expr(*collection);
                let start = start.map(|x| self.expr(*x));
                let stop = stop.map(|x| self.expr(*x));
                let stride = stride.map(|x| self.expr(*x));
                ExprCompiledValue::Slice(box (collection, start, stop, stride))
            }
            ExprP::Not(expr) => {
                let expr = self.expr(*expr);
                return ExprCompiledValue::not(span, expr);
            }
            ExprP::Minus(expr) => {
                let expr = self.expr(*expr);
                ExprCompiledValue::minus(expr)
            }
            ExprP::Plus(expr) => {
                let expr = self.expr(*expr);
                match expr.as_value() {
                    Some(x) if x.unpack_int().is_some() => value!(x),
                    _ => ExprCompiledValue::Plus(box expr),
                }
            }
            ExprP::BitNot(expr) => {
                let expr = self.expr(*expr);
                ExprCompiledValue::BitNot(box expr)
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
                    // ExprCompiledValue::Op(span, op, box(l, r))
                    match op {
                        BinOp::Or => return ExprCompiledValue::or(l, r),
                        BinOp::And => return ExprCompiledValue::and(l, r),
                        BinOp::Equal => eval_equals(l, r, MaybeNot::Id),
                        BinOp::NotEqual => eval_equals(l, r, MaybeNot::Not),
                        BinOp::Less => eval_compare(l, r, CompareOp::Less),
                        BinOp::Greater => eval_compare(l, r, CompareOp::Greater),
                        BinOp::LessOrEqual => eval_compare(l, r, CompareOp::LessOrEqual),
                        BinOp::GreaterOrEqual => eval_compare(l, r, CompareOp::GreaterOrEqual),
                        BinOp::In => ExprCompiledValue::Op(ExprBinOp::In, box (l, r)),
                        BinOp::NotIn => ExprCompiledValue::Op(ExprBinOp::NotIn, box (l, r)),
                        BinOp::Subtract => ExprCompiledValue::Op(ExprBinOp::Sub, box (l, r)),
                        BinOp::Add => ExprCompiledValue::Op(ExprBinOp::Add, box (l, r)),
                        BinOp::Multiply => ExprCompiledValue::Op(ExprBinOp::Multiply, box (l, r)),
                        BinOp::Percent => self.percent(l, r),
                        BinOp::Divide => ExprCompiledValue::Op(ExprBinOp::Divide, box (l, r)),
                        BinOp::FloorDivide => {
                            ExprCompiledValue::Op(ExprBinOp::FloorDivide, box (l, r))
                        }
                        BinOp::BitAnd => ExprCompiledValue::Op(ExprBinOp::BitAnd, box (l, r)),
                        BinOp::BitOr => ExprCompiledValue::Op(ExprBinOp::BitOr, box (l, r)),
                        BinOp::BitXor => ExprCompiledValue::Op(ExprBinOp::BitXor, box (l, r)),
                        BinOp::LeftShift => ExprCompiledValue::Op(ExprBinOp::LeftShift, box (l, r)),
                        BinOp::RightShift => {
                            ExprCompiledValue::Op(ExprBinOp::RightShift, box (l, r))
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
        };
        Spanned { node: expr, span }
    }
}
