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
    environment::slots::ModuleSlotId,
    errors::did_you_mean::did_you_mean,
    eval::{
        compiler::{
            scope::{AssignCount, Captured, CstExpr, ResolvedIdent, Slot},
            Compiler,
        },
        fragment::{
            call::{ArgsCompiledValue, CallCompiled},
            compr::ComprCompiled,
            def::{DefCompiled, InlineDefBody},
            known::list_to_tuple,
            stmt::OptimizeOnFreezeContext,
        },
        runtime::slots::LocalSlotId,
        FrozenDef,
    },
    syntax::ast::{AstExprP, AstLiteral, AstPayload, AstString, BinOp, ExprP, StmtP},
    values::{
        function::BoundMethodGen,
        string::interpolation::parse_percent_s_one,
        types::{
            float::StarlarkFloat, list::List, range::Range, tuple::Tuple,
            unbound::MaybeUnboundValue,
        },
        FrozenHeap, FrozenStringValue, FrozenValue, Heap, Value, ValueError, ValueLike,
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
    /// `x == y`
    Equals(Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>),
    /// `cmp(x <=> y)`
    Compare(
        Box<(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)>,
        CompareOp,
    ),
    /// `type(x)`
    Type(Box<Spanned<ExprCompiledValue>>),
    /// `len(x)`
    Len(Box<Spanned<ExprCompiledValue>>),
    /// `type(x) == "y"`
    TypeIs(Box<Spanned<ExprCompiledValue>>, FrozenStringValue),
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

    /// Result of this expression is definitely `bool`
    /// (if `false` it may also be `bool`).
    fn is_definitely_bool(&self) -> bool {
        match self {
            Self::Value(v) => v.unpack_bool().is_some(),
            Self::Equals(..)
            | Self::TypeIs(..)
            | Self::Not(..)
            | Self::Compare(..)
            | Self::Op(ExprBinOp::In, ..) => true,
            _ => false,
        }
    }
}

impl Spanned<ExprCompiledValue> {
    pub(crate) fn optimize_on_freeze(
        &self,
        ctx: &OptimizeOnFreezeContext,
    ) -> Spanned<ExprCompiledValue> {
        let span = self.span;
        let expr = match self.node {
            ref e @ (ExprCompiledValue::Value(..)
            | ExprCompiledValue::Local(..)
            | ExprCompiledValue::LocalCaptured(..)) => e.clone(),
            ExprCompiledValue::Module(slot) => {
                match ctx.module.get_module_data().get_slot(slot) {
                    None => {
                        // Let if fail at runtime.
                        ExprCompiledValue::Module(slot)
                    }
                    Some(v) => ExprCompiledValue::Value(v),
                }
            }
            ExprCompiledValue::Equals(box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(ctx);
                let r = r.optimize_on_freeze(ctx);
                eval_equals(l, r)
            }
            ExprCompiledValue::Compare(box (ref l, ref r), cmp) => {
                let l = l.optimize_on_freeze(ctx);
                let r = r.optimize_on_freeze(ctx);
                ExprCompiledValue::Compare(box (l, r), cmp)
            }
            ExprCompiledValue::Type(box ref e) => {
                ExprCompiledValue::Type(box e.optimize_on_freeze(ctx))
            }
            ExprCompiledValue::Len(box ref e) => {
                ExprCompiledValue::Len(box e.optimize_on_freeze(ctx))
            }
            ExprCompiledValue::TypeIs(box ref e, t) => {
                ExprCompiledValue::TypeIs(box e.optimize_on_freeze(ctx), t)
            }
            ExprCompiledValue::Tuple(ref xs) => {
                ExprCompiledValue::tuple(xs.map(|e| e.optimize_on_freeze(ctx)), ctx.frozen_heap)
            }
            ExprCompiledValue::List(ref xs) => {
                ExprCompiledValue::List(xs.map(|e| e.optimize_on_freeze(ctx)))
            }
            ExprCompiledValue::Dict(ref kvs) => ExprCompiledValue::Dict(
                kvs.map(|(k, v)| (k.optimize_on_freeze(ctx), v.optimize_on_freeze(ctx))),
            ),
            ExprCompiledValue::Compr(ref compr) => compr.optimize_on_freeze(ctx),
            ExprCompiledValue::Dot(box ref object, ref field) => ExprCompiledValue::dot(
                object.optimize_on_freeze(ctx),
                field,
                ctx.heap,
                ctx.frozen_heap,
            ),
            ExprCompiledValue::ArrayIndirection(box (ref array, ref index)) => {
                let array = array.optimize_on_freeze(ctx);
                let index = index.optimize_on_freeze(ctx);
                ExprCompiledValue::ArrayIndirection(box (array, index))
            }
            ExprCompiledValue::If(box (ref cond, ref t, ref f)) => {
                let cond = cond.optimize_on_freeze(ctx);
                let t = t.optimize_on_freeze(ctx);
                let f = f.optimize_on_freeze(ctx);
                return ExprCompiledValue::if_expr(cond, t, f);
            }
            ExprCompiledValue::Slice(box (ref v, ref start, ref stop, ref step)) => {
                let v = v.optimize_on_freeze(ctx);
                let start = start.as_ref().map(|x| x.optimize_on_freeze(ctx));
                let stop = stop.as_ref().map(|x| x.optimize_on_freeze(ctx));
                let step = step.as_ref().map(|x| x.optimize_on_freeze(ctx));
                ExprCompiledValue::Slice(box (v, start, stop, step))
            }
            ExprCompiledValue::Not(box ref e) => {
                let e = e.optimize_on_freeze(ctx);
                return ExprCompiledValue::not(span, e);
            }
            ExprCompiledValue::Minus(box ref e) => {
                let e = e.optimize_on_freeze(ctx);
                ExprCompiledValue::minus(e)
            }
            ExprCompiledValue::Plus(box ref e) => {
                ExprCompiledValue::Plus(box e.optimize_on_freeze(ctx))
            }
            ExprCompiledValue::BitNot(box ref e) => {
                ExprCompiledValue::BitNot(box e.optimize_on_freeze(ctx))
            }
            ExprCompiledValue::And(box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(ctx);
                let r = r.optimize_on_freeze(ctx);
                return ExprCompiledValue::and(l, r);
            }
            ExprCompiledValue::Or(box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(ctx);
                let r = r.optimize_on_freeze(ctx);
                return ExprCompiledValue::or(l, r);
            }
            ExprCompiledValue::Op(op, box (ref l, ref r)) => {
                let l = l.optimize_on_freeze(ctx);
                let r = r.optimize_on_freeze(ctx);
                ExprCompiledValue::Op(op, box (l, r))
            }
            ExprCompiledValue::PercentSOne(box (before, ref arg, after)) => {
                let arg = arg.optimize_on_freeze(ctx);
                ExprCompiledValue::PercentSOne(box (before, arg, after))
            }
            ExprCompiledValue::FormatOne(box (before, ref arg, after)) => {
                let arg = arg.optimize_on_freeze(ctx);
                ExprCompiledValue::FormatOne(box (before, arg, after))
            }
            ref d @ ExprCompiledValue::Def(..) => d.clone(),
            ExprCompiledValue::Call(ref call) => call.optimize_on_freeze(ctx),
        };
        Spanned { node: expr, span }
    }
}

impl ExprCompiledValue {
    fn not(span: Span, expr: Spanned<ExprCompiledValue>) -> Spanned<ExprCompiledValue> {
        match expr.node {
            ExprCompiledValue::Value(x) => Spanned {
                node: value!(FrozenValue::new_bool(!x.to_value().to_bool())),
                span,
            },
            // Collapse `not not e` to `e` only if `e` is known to produce a boolean.
            ExprCompiledValue::Not(box ref e) if e.is_definitely_bool() => e.clone(),
            _ => Spanned {
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

    fn percent(
        l: Spanned<ExprCompiledValue>,
        r: Spanned<ExprCompiledValue>,
        frozen_heap: &FrozenHeap,
    ) -> ExprCompiledValue {
        if let Some(v) = l.as_string() {
            if let Some((before, after)) = parse_percent_s_one(&v) {
                let before = frozen_heap.alloc_string_value(&before);
                let after = frozen_heap.alloc_string_value(&after);
                return ExprCompiledValue::PercentSOne(box (before, r, after));
            }
        }
        ExprCompiledValue::Op(ExprBinOp::Percent, box (l, r))
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

    fn try_values(
        span: Span,
        values: &[Value],
        heap: &FrozenHeap,
    ) -> Option<Vec<Spanned<ExprCompiledValue>>> {
        values
            .try_map(|v| {
                Self::try_value(span, *v, heap)
                    .map(|expr| Spanned { span, node: expr })
                    .ok_or(())
            })
            .ok()
    }

    /// Try convert a maybe not frozen value to an expression, or discard it.
    pub(crate) fn try_value(span: Span, v: Value, heap: &FrozenHeap) -> Option<ExprCompiledValue> {
        if let Some(v) = v.unpack_frozen() {
            // If frozen, we are lucky.
            Some(ExprCompiledValue::Value(v))
        } else if let Some(v) = v.unpack_str() {
            // If string, copy it to frozen heap.
            Some(ExprCompiledValue::Value(heap.alloc_str(v)))
        } else if let Some(v) = v.downcast_ref::<StarlarkFloat>() {
            Some(ExprCompiledValue::Value(heap.alloc_float(*v)))
        } else if let Some(v) = v.downcast_ref::<Range>() {
            Some(ExprCompiledValue::Value(heap.alloc(*v)))
        } else if let Some(v) = List::from_value(v) {
            // When spec-safe function returned a non-frozen list,
            // we try to convert that list to a list of constants instruction.
            let items = Self::try_values(span, v.content(), heap)?;
            Some(ExprCompiledValue::List(items))
        } else if let Some(v) = Tuple::from_value(v) {
            let items = Self::try_values(span, v.content(), heap)?;
            Some(Self::tuple(items, heap))
        } else {
            None
        }
    }

    /// Construct tuple expression from elements optimizing to frozen tuple value when possible.
    pub(crate) fn tuple(
        elems: Vec<Spanned<ExprCompiledValue>>,
        heap: &FrozenHeap,
    ) -> ExprCompiledValue {
        if let Ok(elems) = elems.try_map(|e| e.as_value().ok_or(())) {
            ExprCompiledValue::Value(heap.alloc_tuple(&elems))
        } else {
            ExprCompiledValue::Tuple(elems)
        }
    }

    pub(crate) fn call(
        span: Span,
        fun: ExprCompiledValue,
        args: ArgsCompiledValue,
    ) -> ExprCompiledValue {
        if let (Some(fun), Some(pos)) = (fun.as_value(), args.one_pos()) {
            // Try to inline a function like `lambda x: type(x) == "y"`.
            if let Some(fun) = fun.downcast_ref::<FrozenDef>() {
                if let Some(InlineDefBody::ReturnTypeIs(t)) = &fun.def_info.inline_def_body {
                    return ExprCompiledValue::TypeIs(box pos.clone(), *t);
                }
            }
        }

        ExprCompiledValue::Call(Spanned {
            span,
            node: CallCompiled::Call(box (Spanned { span, node: fun }, args)),
        })
    }

    pub(crate) fn compile_time_getattr(
        left: FrozenValue,
        attr: &Symbol,
        heap: &Heap,
        frozen_heap: &FrozenHeap,
    ) -> Option<FrozenValue> {
        // We assume `getattr` has no side effects.
        let v = get_attr_hashed_raw(left.to_value(), attr, heap).ok()?;
        match MaybeUnboundValue::new(v.unpack_frozen()?) {
            MaybeUnboundValue::Bound(v) => Some(v),
            MaybeUnboundValue::Attr(..) => None,
            MaybeUnboundValue::Method(m) => {
                Some(frozen_heap.alloc_simple(BoundMethodGen::new(left, m)))
            }
        }
    }

    fn dot(
        object: Spanned<ExprCompiledValue>,
        field: &Symbol,
        heap: &Heap,
        frozen_heap: &FrozenHeap,
    ) -> ExprCompiledValue {
        if let Some(left) = object.as_value() {
            if let Some(v) = Self::compile_time_getattr(left, field, heap, frozen_heap) {
                return ExprCompiledValue::Value(v);
            }
        }

        ExprCompiledValue::Dot(box object, field.clone())
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
                    node: ExprCompiledValue::TypeIs(l, r),
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

fn eval_equals(l: Spanned<ExprCompiledValue>, r: Spanned<ExprCompiledValue>) -> ExprCompiledValue {
    if let (Some(l), Some(r)) = (l.as_value(), r.as_value()) {
        // If comparison fails, let it fail in runtime.
        if let Ok(r) = l.equals(r.to_value()) {
            return value!(FrozenValue::new_bool(r));
        }
    }

    let (l, r) = match try_eval_type_is(l, r) {
        Ok(e) => return e.node,
        Err((l, r)) => (l, r),
    };

    let (r, l) = match try_eval_type_is(r, l) {
        Ok(e) => return e.node,
        Err((r, l)) => (r, l),
    };

    ExprCompiledValue::Equals(box (l, r))
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

pub(crate) fn get_attr_hashed_raw<'v>(
    x: Value<'v>,
    attribute: &Symbol,
    heap: &'v Heap,
) -> anyhow::Result<Value<'v>> {
    let aref = x.get_ref();
    if let Some(methods) = aref.get_methods() {
        if let Some(v) = methods.get_frozen_symbol(attribute) {
            return Ok(v.to_value());
        }
    }
    match aref.get_attr(attribute.as_str(), heap) {
        None => Err(get_attr_no_attr_error(x, attribute)),
        Some(x) => Ok(x),
    }
}

pub(crate) fn get_attr_hashed_bind<'v>(
    x: Value<'v>,
    attribute: &Symbol,
    heap: &'v Heap,
) -> anyhow::Result<Value<'v>> {
    let aref = x.get_ref();
    if let Some(methods) = aref.get_methods() {
        if let Some(v) = methods.get_frozen_symbol(attribute) {
            return MaybeUnboundValue::new(v)
                .to_maybe_unbound_value()
                .bind(x, heap);
        }
    }
    match aref.get_attr(attribute.as_str(), heap) {
        None => Err(get_attr_no_attr_error(x, attribute)),
        Some(x) => {
            // Only `get_methods` is allowed to return unbound methods,
            // so we assume the value is bound here.
            // TODO(nga): if `NativeMethod` or `NativeAttribute` is returned from `get_attr`,
            //   we get an inconsistency between handling of unbound objects
            //   in various call sites in the crate.
            //   However, `NativeMethod` and `NativeAttribute` are not actually useful
            //   as Starlark values, and can be hidden from public API and can be made
            //   to never appear as user-visible values.
            //   Do that.
            //   Alternatively, allow `NativeMethod` and `NativeAttribute` here,
            //   but that would have negative performance implications.
            Ok(x)
        }
    }
}

impl Compiler<'_, '_, '_> {
    pub fn expr_opt(&mut self, expr: Option<Box<CstExpr>>) -> Option<Spanned<ExprCompiledValue>> {
        expr.map(|v| self.expr(*v))
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
                    if let Some(v) = self.eval.module_env.slots().get_slot(slot) {
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
                ExprCompiledValue::tuple(xs, self.eval.module_env.frozen_heap())
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

                ExprCompiledValue::dot(
                    left,
                    &s,
                    self.eval.module_env.heap(),
                    self.eval.module_env.frozen_heap(),
                )
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
                    let val = self.eval.module_env.frozen_heap().alloc(x);
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
                        BinOp::Equal => eval_equals(l, r),
                        BinOp::NotEqual => {
                            ExprCompiledValue::not(
                                span,
                                Spanned {
                                    span,
                                    node: eval_equals(l, r),
                                },
                            )
                            .node
                        }
                        BinOp::Less => eval_compare(l, r, CompareOp::Less),
                        BinOp::Greater => eval_compare(l, r, CompareOp::Greater),
                        BinOp::LessOrEqual => eval_compare(l, r, CompareOp::LessOrEqual),
                        BinOp::GreaterOrEqual => eval_compare(l, r, CompareOp::GreaterOrEqual),
                        BinOp::In => ExprCompiledValue::Op(ExprBinOp::In, box (l, r)),
                        BinOp::NotIn => {
                            ExprCompiledValue::not(
                                span,
                                Spanned {
                                    span,
                                    node: ExprCompiledValue::Op(ExprBinOp::In, box (l, r)),
                                },
                            )
                            .node
                        }
                        BinOp::Subtract => ExprCompiledValue::Op(ExprBinOp::Sub, box (l, r)),
                        BinOp::Add => ExprCompiledValue::Op(ExprBinOp::Add, box (l, r)),
                        BinOp::Multiply => ExprCompiledValue::Op(ExprBinOp::Multiply, box (l, r)),
                        BinOp::Percent => {
                            ExprCompiledValue::percent(l, r, self.eval.module_env.frozen_heap())
                        }
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
                let val = x.compile(self.eval.module_env.frozen_heap());
                value!(val)
            }
        };
        Spanned { node: expr, span }
    }
}
