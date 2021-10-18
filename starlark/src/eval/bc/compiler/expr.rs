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

//! Compile expressions.

use std::collections::HashSet;

use gazebo::prelude::*;

use crate::{
    codemap::{Span, Spanned},
    collections::{Hashed, SmallMap},
    eval::{
        bc::{
            instr_arg::{ArgPopsStack, ArgPopsStack1, ArgPopsStackMaybe1},
            instr_impl::*,
            writer::BcWriter,
        },
        fragment::expr::{CompareOp, ExprBinOp, ExprCompiledValue, MaybeNot},
    },
    values::{FrozenValue, ValueLike},
};

pub(crate) fn write_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a Spanned<ExprCompiledValue>>,
    bc: &mut BcWriter,
) {
    for expr in exprs {
        expr.write_bc(bc);
    }
}

impl Spanned<ExprCompiledValue> {
    fn try_dict_of_consts(
        xs: &[(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)],
    ) -> Option<SmallMap<FrozenValue, FrozenValue>> {
        let mut res = SmallMap::new();
        for (k, v) in xs {
            let k = k.as_value()?.get_hashed().ok()?;
            let v = v.as_value()?;
            let prev = res.insert_hashed(k, v);
            if prev.is_some() {
                // If there are duplicates, so don't take the fast-literal
                // path and go down the slow runtime path (which will raise the error).
                // We have a lint that will likely fire on this issue (and others).
                return None;
            }
        }
        Some(res)
    }

    fn try_dict_const_keys(
        xs: &[(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)],
    ) -> Option<Box<[Hashed<FrozenValue>]>> {
        let mut keys = Vec::new();
        let mut keys_unique = HashSet::new();
        for (k, _) in xs {
            let k = k.as_value()?.get_hashed().ok()?;
            keys.push(k);
            let inserted = keys_unique.insert(k);
            if !inserted {
                // Otherwise fail at runtime
                return None;
            }
        }
        Some(keys.into_boxed_slice())
    }

    fn write_dict(
        span: Span,
        xs: &[(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>)],
        bc: &mut BcWriter,
    ) {
        if xs.is_empty() {
            bc.write_instr::<InstrDictNew>(span, ());
        } else if let Some(d) = Self::try_dict_of_consts(xs) {
            bc.write_instr::<InstrDictOfConsts>(span, d);
        } else if let Some(keys) = Self::try_dict_const_keys(xs) {
            assert_eq!(keys.len(), xs.len());
            write_exprs(xs.iter().map(|(_, v)| v), bc);
            bc.write_instr::<InstrDictConstKeys>(span, (ArgPopsStack(xs.len() as u32), keys));
        } else {
            let key_spans = xs.map(|(k, _v)| k.span);
            let key_spans = bc.alloc_any(key_spans);
            write_exprs(xs.iter().flat_map(|(k, v)| [k, v]), bc);
            bc.write_instr::<InstrDictNPop>(span, (ArgPopsStack(xs.len() as u32 * 2), key_spans));
        }
    }

    pub(crate) fn write_bc(&self, bc: &mut BcWriter) {
        let span = self.span;
        match self.node {
            ExprCompiledValue::Value(v) => {
                bc.write_const(span, v);
            }
            ExprCompiledValue::Local(slot) => {
                bc.write_load_local(span, slot);
            }
            ExprCompiledValue::LocalCaptured(slot) => {
                bc.write_instr::<InstrLoadLocalCaptured>(span, slot);
            }
            ExprCompiledValue::Module(slot) => {
                bc.write_instr::<InstrLoadModule>(span, slot);
            }
            ExprCompiledValue::Equals(box (ref a, ref b), maybe_not) => {
                a.write_bc(bc);
                b.write_bc(bc);
                match maybe_not {
                    MaybeNot::Id => bc.write_instr::<InstrEq>(span, ()),
                    MaybeNot::Not => bc.write_instr::<InstrNotEq>(span, ()),
                }
            }
            ExprCompiledValue::Compare(box (ref l, ref r), cmp) => {
                l.write_bc(bc);
                r.write_bc(bc);
                match cmp {
                    CompareOp::Less => bc.write_instr::<InstrLess>(span, ()),
                    CompareOp::Greater => bc.write_instr::<InstrGreater>(span, ()),
                    CompareOp::LessOrEqual => bc.write_instr::<InstrLessOrEqual>(span, ()),
                    CompareOp::GreaterOrEqual => bc.write_instr::<InstrGreaterOrEqual>(span, ()),
                }
            }
            ExprCompiledValue::Type(box ref expr) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrType>(span, ());
            }
            ExprCompiledValue::Len(box ref expr) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrLen>(span, ());
            }
            ExprCompiledValue::TypeIs(box ref v, t, maybe_not) => {
                v.write_bc(bc);
                bc.write_instr::<InstrTypeIs>(Span::default(), t);
                if maybe_not == MaybeNot::Not {
                    bc.write_instr::<InstrNot>(Span::default(), ());
                }
            }
            ExprCompiledValue::Tuple(ref xs) => {
                write_exprs(xs, bc);
                bc.write_instr::<InstrTupleNPop>(span, ArgPopsStack(xs.len() as u32));
            }
            ExprCompiledValue::List(ref xs) => {
                if xs.is_empty() {
                    bc.write_instr::<InstrListNew>(span, ());
                } else if xs.iter().all(|x| x.as_value().is_some()) {
                    let content = xs.map(|v| v.as_value().unwrap()).into_boxed_slice();
                    bc.write_instr::<InstrListOfConsts>(span, content);
                } else {
                    write_exprs(xs, bc);
                    bc.write_instr::<InstrListNPop>(span, ArgPopsStack(xs.len() as u32));
                }
            }
            ExprCompiledValue::Dict(ref xs) => Self::write_dict(span, xs, bc),
            ExprCompiledValue::Compr(ref compr) => {
                compr.write_bc(span, bc);
            }
            ExprCompiledValue::Dot(box ref object, ref field) => {
                object.write_bc(bc);
                bc.write_instr::<InstrObjectField>(span, field.clone());
            }
            ExprCompiledValue::ArrayIndirection(box (ref array, ref index)) => {
                array.write_bc(bc);
                index.write_bc(bc);
                bc.write_instr::<InstrArrayIndex>(span, ());
            }
            ExprCompiledValue::Slice(box (ref l, ref start, ref stop, ref step)) => {
                l.write_bc(bc);
                write_exprs([start, stop, step].iter().copied().flatten(), bc);
                bc.write_instr::<InstrSlice>(
                    span,
                    (
                        ArgPopsStack1,
                        ArgPopsStackMaybe1(start.is_some()),
                        ArgPopsStackMaybe1(stop.is_some()),
                        ArgPopsStackMaybe1(step.is_some()),
                    ),
                );
            }
            ExprCompiledValue::Not(box ref expr) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrNot>(span, ());
            }
            ExprCompiledValue::Minus(box ref expr) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrMinus>(span, ());
            }
            ExprCompiledValue::Plus(box ref expr) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrPlus>(span, ());
            }
            ExprCompiledValue::BitNot(box ref expr) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrBitNot>(span, ());
            }
            ExprCompiledValue::If(box (ref cond, ref t, ref f)) => {
                cond.write_bc(bc);
                let else_patch = bc.write_if_not_br(cond.span);
                t.write_bc(bc);

                // Both then and else branches leave a value on the stack.
                // But we execute either of them.
                // So explicitly decrement stack size.
                bc.stack_sub(1);

                let end_patch = bc.write_br(Span::default());
                bc.patch_addr(else_patch);
                f.write_bc(bc);
                bc.patch_addr(end_patch);
            }
            ExprCompiledValue::And(box (ref l, ref r)) => {
                l.write_bc(bc);
                bc.write_instr::<InstrDup>(span, ());
                bc.write_if(l.span, |bc| {
                    bc.write_instr::<InstrPop>(span, ());
                    r.write_bc(bc);
                });
            }
            ExprCompiledValue::Or(box (ref l, ref r)) => {
                l.write_bc(bc);
                bc.write_instr::<InstrDup>(span, ());
                bc.write_if_not(l.span, |bc| {
                    bc.write_instr::<InstrPop>(l.span, ());
                    r.write_bc(bc);
                });
            }
            ExprCompiledValue::Op(op, box (ref l, ref r)) => {
                l.write_bc(bc);
                r.write_bc(bc);
                match op {
                    ExprBinOp::In => bc.write_instr::<InstrIn>(span, ()),
                    ExprBinOp::NotIn => bc.write_instr::<InstrNotIn>(span, ()),
                    ExprBinOp::Sub => bc.write_instr::<InstrSub>(span, ()),
                    ExprBinOp::Add => bc.write_instr::<InstrAdd>(span, ()),
                    ExprBinOp::Multiply => bc.write_instr::<InstrMultiply>(span, ()),
                    ExprBinOp::Divide => bc.write_instr::<InstrDivide>(span, ()),
                    ExprBinOp::FloorDivide => bc.write_instr::<InstrFloorDivide>(span, ()),
                    ExprBinOp::Percent => bc.write_instr::<InstrPercent>(span, ()),
                    ExprBinOp::BitAnd => bc.write_instr::<InstrBitAnd>(span, ()),
                    ExprBinOp::BitOr => bc.write_instr::<InstrBitOr>(span, ()),
                    ExprBinOp::BitXor => bc.write_instr::<InstrBitXor>(span, ()),
                    ExprBinOp::LeftShift => bc.write_instr::<InstrLeftShift>(span, ()),
                    ExprBinOp::RightShift => bc.write_instr::<InstrRightShift>(span, ()),
                }
            }
            ExprCompiledValue::PercentSOne(box (before, ref arg, after)) => {
                arg.write_bc(bc);
                bc.write_instr::<InstrPercentSOne>(span, (before, after));
            }
            ExprCompiledValue::FormatOne(box (before, ref arg, after)) => {
                arg.write_bc(bc);
                bc.write_instr::<InstrFormatOne>(span, (before, after));
            }
            ExprCompiledValue::Call(ref call) => call.write_bc(bc),
            ExprCompiledValue::Def(ref def) => def.write_bc(bc),
        }
    }

    pub(crate) fn write_bc_for_effect(&self, bc: &mut BcWriter) {
        self.write_bc(bc);
        bc.write_instr::<InstrPop>(self.span, ());
    }
}
