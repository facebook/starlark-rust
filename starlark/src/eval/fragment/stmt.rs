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

//! Evaluation environment, provide converters from Ast* element to value.
//!
//! # <a name="build_file"></a>Starlark and BUILD dialect
//!
//! All evaluation function can evaluate the full Starlark language (i.e.
//! Bazel's .bzl files) or the BUILD file dialect (i.e. used to interpret
//! Bazel's BUILD file). The BUILD dialect does not allow `def` statements.
use crate::{
    codemap::{Span, Spanned},
    environment::{slots::ModuleSlotId, FrozenModuleRef},
    eval::{
        compiler::{
            expr_throw,
            scope::{Captured, CstAssign, CstExpr, CstStmt, Slot},
            throw, Compiler, EvalException, ExprEvalException,
        },
        fragment::{expr::ExprCompiledValue, known::list_to_tuple},
        runtime::{
            evaluator::{Evaluator, GC_THRESHOLD},
            slots::LocalSlotId,
        },
    },
    syntax::ast::{AssignOp, AssignP, StmtP},
    values::{list::List, Heap, Value, ValueError},
};
use anyhow::anyhow;
use gazebo::prelude::*;
use std::mem;
use thiserror::Error;

pub(crate) type StmtCompiled =
    Box<dyn for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>> + Send + Sync>;

#[derive(Clone)]
pub(crate) enum AssignModifyLhs {
    Dot(Spanned<ExprCompiledValue>, String),
    Array(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>),
    Local(Spanned<(LocalSlotId, Captured)>),
    Module(Spanned<ModuleSlotId>),
}

#[derive(Clone)]
pub(crate) enum StmtCompiledValue {
    PossibleGc,
    Return(Option<Spanned<ExprCompiledValue>>),
    Expr(Spanned<ExprCompiledValue>),
    Assign(Spanned<AssignCompiledValue>, Spanned<ExprCompiledValue>),
    AssignModify(AssignModifyLhs, AssignOp, Spanned<ExprCompiledValue>),
    If(Box<(Spanned<ExprCompiledValue>, StmtsCompiled, StmtsCompiled)>),
    For(
        Box<(
            Spanned<AssignCompiledValue>,
            Spanned<ExprCompiledValue>,
            StmtsCompiled,
        )>,
    ),
    Break,
    Continue,
}

#[derive(Debug)]
pub(crate) struct StmtCompileContext {
    pub(crate) has_before_stmt: bool,
}

impl StmtCompileContext {
    fn maybe_wrap_before_stmt(&self, span: Span, stmt: StmtCompiled) -> StmtCompiled {
        if self.has_before_stmt {
            box move |eval| {
                before_stmt(span, eval);
                stmt(eval)
            }
        } else {
            stmt
        }
    }
}

impl Spanned<StmtCompiledValue> {
    pub(crate) fn as_compiled(&self, compiler: &StmtCompileContext) -> StmtCompiled {
        let span = self.span;
        match self.node {
            StmtCompiledValue::PossibleGc => box move |eval| {
                possible_gc(eval);
                Ok(())
            },
            StmtCompiledValue::Return(None) => {
                stmt!(compiler, "return_none", span, |_eval| {
                    return Err(EvalException::Return(Value::new_none()));
                })
            }
            StmtCompiledValue::Return(Some(ref e)) => {
                let e = e.as_compiled();
                stmt!(compiler, "return", span, |eval| {
                    return Err(EvalException::Return(e(eval)?));
                })
            }
            StmtCompiledValue::Expr(ref e) => {
                let e = e.as_compiled();
                stmt!(compiler, "expr", span, |eval| {
                    e(eval)?;
                })
            }
            StmtCompiledValue::Assign(ref lhs, ref rhs) => {
                let lhs = lhs.as_compiled();
                let rhs = rhs.as_compiled();
                stmt!(compiler, "assign", span, |eval| {
                    lhs(rhs(eval)?, eval)?;
                })
            }
            StmtCompiledValue::AssignModify(AssignModifyLhs::Dot(ref e, ref s), op, ref rhs) => {
                let span_stmt = span;
                let span_lhs = e.span;
                let e = e.as_compiled();
                let s = s.clone();
                let op = op.as_fn();
                let rhs = rhs.as_compiled();
                stmt!(compiler, "assign_dot", span_stmt, |eval| {
                    let e: Value = e(eval)?;
                    let (_, v) = throw(e.get_attr_error(&s, eval.heap()), span_lhs, eval)?;
                    let rhs = rhs(eval)?;
                    throw(
                        e.set_attr(&s, throw(op(v, rhs, eval), span_stmt, eval)?),
                        span_stmt,
                        eval,
                    )?;
                })
            }
            StmtCompiledValue::AssignModify(
                AssignModifyLhs::Array(ref lhs, ref idx),
                op,
                ref rhs,
            ) => {
                let span_stmt = span;
                let span_lhs = lhs.span;
                let e = lhs.as_compiled();
                let idx = idx.as_compiled();
                let op = op.as_fn();
                let rhs = rhs.as_compiled();
                stmt!(compiler, "assign_array", span_stmt, |eval| {
                    let e: Value = e(eval)?;
                    let idx = idx(eval)?;
                    let v = throw(e.at(idx, eval.heap()), span_lhs, eval)?;
                    let rhs = rhs(eval)?;
                    throw(
                        e.set_at(idx, throw(op(v, rhs, eval), span_stmt, eval)?),
                        span_stmt,
                        eval,
                    )?;
                })
            }
            StmtCompiledValue::AssignModify(AssignModifyLhs::Local(ref lhs), op, ref rhs) => {
                let span_stmt = span;
                let span_lhs = lhs.span;
                let (slot, captured) = lhs.node;
                let op = op.as_fn();
                let rhs = rhs.as_compiled();
                match captured {
                    Captured::Yes => stmt!(compiler, "assign_local_captured", span_stmt, |eval| {
                        let v = throw(eval.get_slot_local_captured(slot), span_lhs, eval)?;
                        let rhs = rhs(eval)?;
                        let v = throw(op(v, rhs, eval), span_stmt, eval)?;
                        eval.set_slot_local_captured(slot, v);
                    }),
                    Captured::No => stmt!(compiler, "assign_local", span_stmt, |eval| {
                        let v = throw(eval.get_slot_local(slot), span_lhs, eval)?;
                        let rhs = rhs(eval)?;
                        let v = throw(op(v, rhs, eval), span_stmt, eval)?;
                        eval.set_slot_local(slot, v);
                    }),
                }
            }
            StmtCompiledValue::AssignModify(AssignModifyLhs::Module(lhs), op, ref rhs) => {
                let span_stmt = span;
                let span_lhs = lhs.span;
                let slot = lhs.node;
                let op = op.as_fn();
                let rhs = rhs.as_compiled();
                stmt!(compiler, "assign_module", span_stmt, |eval| {
                    let v = throw(eval.get_slot_module(slot), span_lhs, eval)?;
                    let rhs = rhs(eval)?;
                    let v = throw(op(v, rhs, eval), span_stmt, eval)?;
                    eval.set_slot_module(slot, v);
                })
            }
            StmtCompiledValue::If(box (ref cond, ref then_block, ref else_block)) => {
                let cond = cond.as_compiled();
                if else_block.is_empty() {
                    let then_block = then_block.as_compiled(compiler);
                    stmt!(compiler, "if_then", span, |eval| if cond(eval)?.to_bool() {
                        then_block(eval)?
                    })
                } else if then_block.is_empty() {
                    let else_block = else_block.as_compiled(compiler);
                    stmt!(
                        compiler,
                        "if_not_then",
                        span,
                        |eval| if !cond(eval)?.to_bool() {
                            else_block(eval)?
                        }
                    )
                } else {
                    let then_block = then_block.as_compiled(compiler);
                    let else_block = else_block.as_compiled(compiler);
                    stmt!(
                        compiler,
                        "if_then_else",
                        span,
                        |eval| if cond(eval)?.to_bool() {
                            then_block(eval)?
                        } else {
                            else_block(eval)?
                        }
                    )
                }
            }
            StmtCompiledValue::For(box (ref var, ref over, ref body)) => {
                let var = var.as_compiled();
                let over_span = over.span;
                let over = over.as_compiled();
                let st = body.as_compiled(compiler);
                stmt!(compiler, "for", span, |eval| {
                    let heap = eval.heap();
                    let iterable = over(eval)?;
                    throw(
                        iterable.with_iterator(heap, |it| {
                            for v in it {
                                var(v, eval)?;
                                match st(eval) {
                                    Err(EvalException::Break) => break,
                                    Err(EvalException::Continue) => {}
                                    Err(e) => return Err(e),
                                    _ => {}
                                }
                            }
                            Ok(())
                        }),
                        over_span,
                        eval,
                    )??;
                })
            }
            StmtCompiledValue::Break => stmt!(compiler, "break", span, |_eval| return Err(
                EvalException::Break
            )),
            StmtCompiledValue::Continue => {
                stmt!(compiler, "continue", span, |_eval| return Err(
                    EvalException::Continue
                ))
            }
        }
    }

    fn optimize_on_freeze(&self, module: &FrozenModuleRef) -> StmtsCompiled {
        let span = self.span;
        match self.node {
            StmtCompiledValue::Return(Some(ref e)) => StmtsCompiled::one(Spanned {
                span,
                node: StmtCompiledValue::Return(Some(e.optimize_on_freeze(module))),
            }),
            StmtCompiledValue::Expr(ref expr) => {
                let expr = expr.optimize_on_freeze(module);
                Self::expr(expr)
            }
            StmtCompiledValue::Assign(ref lhs, ref rhs) => {
                let lhs = lhs.optimize_on_freeze(module);
                let rhs = rhs.optimize_on_freeze(module);
                StmtsCompiled::one(Spanned {
                    span,
                    node: StmtCompiledValue::Assign(lhs, rhs),
                })
            }
            StmtCompiledValue::If(box (ref cond, ref t, ref f)) => {
                let cond = cond.optimize_on_freeze(module);
                let t = t.optimize_on_freeze(module);
                let f = f.optimize_on_freeze(module);
                Self::if_stmt(span, cond, t, f)
            }
            StmtCompiledValue::For(box (ref var, ref over, ref body)) => {
                let var = var.optimize_on_freeze(module);
                let over = over.optimize_on_freeze(module);
                let body = body.optimize_on_freeze(module);
                StmtsCompiled::one(Spanned {
                    span,
                    node: StmtCompiledValue::For(box (var, over, body)),
                })
            }
            ref s @ (StmtCompiledValue::PossibleGc
            | StmtCompiledValue::Break
            | StmtCompiledValue::Continue
            | StmtCompiledValue::Return(None)) => StmtsCompiled::one(Spanned {
                span,
                node: s.clone(),
            }),
            ref s @ StmtCompiledValue::AssignModify(..) => StmtsCompiled::one(Spanned {
                span,
                node: s.clone(),
            }),
        }
    }

    fn expr(expr: Spanned<ExprCompiledValue>) -> StmtsCompiled {
        match expr {
            Spanned {
                node: ExprCompiledValue::Value(..),
                ..
            } => StmtsCompiled::empty(),
            expr => StmtsCompiled::one(Spanned {
                span: expr.span,
                node: StmtCompiledValue::Expr(expr),
            }),
        }
    }

    fn if_stmt(
        span: Span,
        cond: Spanned<ExprCompiledValue>,
        t: StmtsCompiled,
        f: StmtsCompiled,
    ) -> StmtsCompiled {
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
            } => Self::if_stmt(span, cond, f, t),
            cond => {
                if t.is_empty() && f.is_empty() {
                    Self::expr(cond)
                } else {
                    StmtsCompiled::one(Spanned {
                        span,
                        node: StmtCompiledValue::If(box (cond, t, f)),
                    })
                }
            }
        }
    }
}

#[derive(Clone)]
enum SmallVec1<T> {
    Empty,
    One(T),
    Many(Vec<T>),
}

impl<T> SmallVec1<T> {
    fn extend(&mut self, stmts: SmallVec1<T>) {
        *self = match (mem::replace(self, SmallVec1::Empty), stmts) {
            (SmallVec1::Empty, right) => right,
            (left, SmallVec1::Empty) => left,
            (SmallVec1::One(left), SmallVec1::One(right)) => SmallVec1::Many(vec![left, right]),
            (SmallVec1::One(left), SmallVec1::Many(mut right)) => {
                right.insert(0, left);
                SmallVec1::Many(right)
            }
            (SmallVec1::Many(mut left), SmallVec1::One(right)) => {
                left.push(right);
                SmallVec1::Many(left)
            }
            (SmallVec1::Many(mut left), SmallVec1::Many(right)) => {
                left.extend(right);
                SmallVec1::Many(left)
            }
        }
    }
}

#[derive(Clone)]
pub(crate) struct StmtsCompiled(SmallVec1<Spanned<StmtCompiledValue>>);

impl StmtsCompiled {
    pub(crate) fn empty() -> StmtsCompiled {
        StmtsCompiled(SmallVec1::Empty)
    }

    pub(crate) fn one(stmt: Spanned<StmtCompiledValue>) -> StmtsCompiled {
        StmtsCompiled(SmallVec1::One(stmt))
    }

    pub(crate) fn is_empty(&self) -> bool {
        match &self.0 {
            SmallVec1::Empty => true,
            SmallVec1::One(_) => false,
            SmallVec1::Many(stmts) => {
                debug_assert!(stmts.len() > 1);
                false
            }
        }
    }

    pub(crate) fn extend(&mut self, right: StmtsCompiled) {
        self.0.extend(right.0);
    }

    pub(crate) fn as_compiled(&self, compiler: &StmtCompileContext) -> StmtCompiled {
        match self.0 {
            SmallVec1::Empty => box |_eval| Ok(()),
            SmallVec1::One(ref stmt) => stmt.as_compiled(compiler),
            SmallVec1::Many(ref vec) => {
                debug_assert!(vec.len() > 1);
                let vec = vec.map(|s| s.as_compiled(compiler));
                box move |eval| {
                    for stmt in &vec {
                        stmt(eval)?;
                    }
                    Ok(())
                }
            }
        }
    }

    pub(crate) fn optimize_on_freeze(&self, module: &FrozenModuleRef) -> StmtsCompiled {
        let mut stmts = StmtsCompiled::empty();
        match &self.0 {
            SmallVec1::Empty => {}
            SmallVec1::One(s) => stmts.extend(s.optimize_on_freeze(module)),
            SmallVec1::Many(ss) => {
                for s in ss {
                    stmts.extend(s.optimize_on_freeze(module));
                }
            }
        }
        stmts
    }

    pub(crate) fn first(&self) -> Option<&Spanned<StmtCompiledValue>> {
        match &self.0 {
            SmallVec1::Empty => None,
            SmallVec1::One(s) => Some(s),
            SmallVec1::Many(ss) => ss.first(),
        }
    }
}

#[derive(Debug, Error)]
enum AssignError {
    // Incorrect number of value to unpack (expected, got)
    #[error("Unpacked {1} values but expected {0}")]
    IncorrectNumberOfValueToUnpack(i32, i32),
}

pub(crate) type AssignCompiled = Box<
    dyn for<'v> Fn(Value<'v>, &mut Evaluator<'v, '_>) -> Result<(), ExprEvalException>
        + Send
        + Sync,
>;
#[derive(Clone)]
pub(crate) enum AssignCompiledValue {
    Dot(Spanned<ExprCompiledValue>, String),
    ArrayIndirection(Spanned<ExprCompiledValue>, Spanned<ExprCompiledValue>),
    Tuple(Vec<Spanned<AssignCompiledValue>>),
    Local(LocalSlotId, Captured),
    Module(ModuleSlotId, String),
}

impl Spanned<AssignCompiledValue> {
    pub(crate) fn as_compiled(&self) -> AssignCompiled {
        let span = self.span;
        match self.node {
            AssignCompiledValue::Dot(ref e, ref s) => {
                let e = e.as_compiled();
                let s = s.clone();
                box move |value, eval| expr_throw(e(eval)?.set_attr(&s, value), span, eval)
            }
            AssignCompiledValue::ArrayIndirection(ref array, ref index) => {
                let array = array.as_compiled();
                let index = index.as_compiled();
                box move |value, eval| {
                    expr_throw(array(eval)?.set_at(index(eval)?, value), span, eval)
                }
            }
            AssignCompiledValue::Tuple(ref v) => {
                let v = v.map(|v| v.as_compiled());
                box move |value, eval| eval_assign_list(&v, span, value, eval)
            }
            AssignCompiledValue::Local(slot, Captured::Yes) => box move |value, eval| {
                eval.set_slot_local_captured(slot, value);
                Ok(())
            },
            AssignCompiledValue::Local(slot, Captured::No) => box move |value, eval| {
                eval.set_slot_local(slot, value);
                Ok(())
            },
            AssignCompiledValue::Module(slot, ref name) => {
                let name = name.clone();
                box move |value, eval| {
                    // Make sure that `ComplexValue`s get their name as soon as possible
                    value.export_as(&name, eval);
                    eval.set_slot_module(slot, value);
                    Ok(())
                }
            }
        }
    }

    pub(crate) fn optimize_on_freeze(
        &self,
        module: &FrozenModuleRef,
    ) -> Spanned<AssignCompiledValue> {
        let span = self.span;
        let assign = match self.node {
            AssignCompiledValue::Dot(ref object, ref field) => {
                let object = object.optimize_on_freeze(module);
                let field = field.clone();
                AssignCompiledValue::Dot(object, field)
            }
            AssignCompiledValue::ArrayIndirection(ref array, ref index) => {
                let array = array.optimize_on_freeze(module);
                let index = index.optimize_on_freeze(module);
                AssignCompiledValue::ArrayIndirection(array, index)
            }
            AssignCompiledValue::Tuple(ref xs) => {
                let xs = xs.map(|x| x.optimize_on_freeze(module));
                AssignCompiledValue::Tuple(xs)
            }
            ref e @ (AssignCompiledValue::Local(..) | AssignCompiledValue::Module(..)) => e.clone(),
        };
        Spanned { node: assign, span }
    }
}

fn eval_assign_list<'v>(
    lvalues: &[AssignCompiled],
    span: Span,
    value: Value<'v>,
    eval: &mut Evaluator<'v, '_>,
) -> Result<(), ExprEvalException> {
    let l = lvalues.len() as i32;
    let nvl = expr_throw(value.length(), span, eval)?;
    if nvl != l {
        expr_throw(
            Err(AssignError::IncorrectNumberOfValueToUnpack(l, nvl).into()),
            span,
            eval,
        )
    } else {
        let mut it1 = lvalues.iter();
        // TODO: the span here should probably include the rvalue
        let mut it2 = expr_throw(value.iterate(eval.heap()), span, eval)?;
        for _ in 0..l {
            it1.next().unwrap()(it2.next().unwrap(), eval)?;
        }
        Ok(())
    }
}

pub(crate) type AssignModifyOpFn =
    for<'v> fn(Value<'v>, Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>>;

impl AssignOp {
    fn as_fn(self) -> AssignModifyOpFn {
        match self {
            AssignOp::Add => |l, r, eval| add_assign(l, r, eval.heap()),
            AssignOp::Subtract => |l, r, eval| l.sub(r, eval.heap()),
            AssignOp::Multiply => |l, r, eval| l.mul(r, eval.heap()),
            AssignOp::Divide => |l, r, eval| l.div(r, eval.heap()),
            AssignOp::FloorDivide => |l, r, eval| l.floor_div(r, eval.heap()),
            AssignOp::Percent => |l, r, eval| l.percent(r, eval.heap()),
            AssignOp::BitAnd => |l, r, _| l.bit_and(r),
            AssignOp::BitOr => |l, r, _| l.bit_or(r),
            AssignOp::BitXor => |l, r, _| l.bit_xor(r),
            AssignOp::LeftShift => |l, r, _| l.left_shift(r),
            AssignOp::RightShift => |l, r, _| l.right_shift(r),
        }
    }
}

impl Compiler<'_> {
    pub fn assign(&mut self, expr: CstAssign) -> Spanned<AssignCompiledValue> {
        let span = expr.span;
        let assign = match expr.node {
            AssignP::Dot(e, s) => {
                let e = self.expr(*e);
                let s = s.node;
                AssignCompiledValue::Dot(e, s)
            }
            AssignP::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e);
                let idx = self.expr(idx);
                AssignCompiledValue::ArrayIndirection(e, idx)
            }
            AssignP::Tuple(v) => {
                let v = v.into_map(|x| self.assign(x));
                AssignCompiledValue::Tuple(v)
            }
            AssignP::Identifier(ident) => {
                let name = ident.node.0;
                let binding_id = ident
                    .node
                    .1
                    .unwrap_or_else(|| panic!("unresolved binding: `{}`", name));
                let binding = self.scope_data.get_binding(binding_id);
                let slot = binding
                    .slot
                    .unwrap_or_else(|| panic!("unresolved binding: `{}`", name));
                match (slot, binding.captured) {
                    (Slot::Local(slot), captured) => AssignCompiledValue::Local(slot, captured),
                    (Slot::Module(slot), _) => AssignCompiledValue::Module(slot, name),
                }
            }
        };
        Spanned { node: assign, span }
    }

    fn assign_modify(
        &mut self,
        span_stmt: Span,
        lhs: CstAssign,
        rhs: Spanned<ExprCompiledValue>,
        op: AssignOp,
    ) -> StmtsCompiled {
        let span_lhs = lhs.span;
        match lhs.node {
            AssignP::Dot(e, s) => {
                let e = self.expr(*e);
                StmtsCompiled::one(Spanned {
                    span: span_stmt,
                    node: StmtCompiledValue::AssignModify(AssignModifyLhs::Dot(e, s.node), op, rhs),
                })
            }
            AssignP::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e);
                let idx = self.expr(idx);
                StmtsCompiled::one(Spanned {
                    span: span_stmt,
                    node: StmtCompiledValue::AssignModify(AssignModifyLhs::Array(e, idx), op, rhs),
                })
            }
            AssignP::Identifier(ident) => {
                let (slot, captured) = self.scope_data.get_assign_ident_slot(&ident);
                match slot {
                    Slot::Local(slot) => {
                        let lhs = Spanned {
                            node: (slot, captured),
                            span: span_lhs,
                        };
                        StmtsCompiled::one(Spanned {
                            span: span_stmt,
                            node: StmtCompiledValue::AssignModify(
                                AssignModifyLhs::Local(lhs),
                                op,
                                rhs,
                            ),
                        })
                    }
                    Slot::Module(slot) => {
                        let lhs = Spanned {
                            node: slot,
                            span: span_lhs,
                        };
                        StmtsCompiled::one(Spanned {
                            span: span_stmt,
                            node: StmtCompiledValue::AssignModify(
                                AssignModifyLhs::Module(lhs),
                                op,
                                rhs,
                            ),
                        })
                    }
                }
            }
            AssignP::Tuple(_) => {
                unreachable!("Assign modify validates that the LHS is never a tuple")
            }
        }
    }
}

// This function should be called before every meaningful statement.
// The purposes are GC, profiling and debugging.
//
// This function is called only if `before_stmt` is set before compilation start.
fn before_stmt(span: Span, eval: &mut Evaluator) {
    assert!(
        !eval.before_stmt.is_empty(),
        "this code should not be called if `before_stmt` is set"
    );
    let fs = mem::take(&mut eval.before_stmt);
    for f in &fs {
        f(span, eval)
    }
    let added = mem::replace(&mut eval.before_stmt, fs);
    assert!(
        added.is_empty(),
        "`before_stmt` cannot be modified during evaluation"
    );
}

// There are two requirements to perform a GC:
//
// 1. We can't be profiling, since profiling relies on the redundant heap
//    entries. When profiling we set disable_gc.
// 2. We must be able to access all roots.
//
// We track as many roots as possible, and eventually aim to track them all, but
// for the moment we're only sure we have all roots when we are in the module
// evaluation eval. There are three roots we don't yet know about:
//
// 1. When evaluating an expression which has multiple subexpressions, e.g. List
//    we can't GC during that, as we can't see the root of the first list.
// 2. When evaluating inside a native function, especially if that native
//    function calls back to a non-native function, e.g. sort with a comparison
//    function.
// 3. When iterating we freeze the iteration variable, which means it
//    can't be moved by a GC. A special type of root.
//
// The first issue can be solved by moving to a bytecode interpreter and
// evaluation stack. The second issue can be solved by disabling GC while in
// such functions (it's probably rare). The third issue could be solved by
// making the freeze for iteration a separate flag to the RefCell, at the cost
// of an extra word in ValueMem. Or we could disable GC while iterating.
//
// For the moment we only GC when executing a statement at the root of the
// module, which we know is safe with respect to all three conditions.
//
// We also require that `extra_v` is None, since otherwise the user might have
// additional values stashed somewhere.
fn possible_gc(eval: &mut Evaluator) {
    if !eval.disable_gc
        && eval.heap().allocated_bytes() >= eval.next_gc_level
        && eval.extra_v.is_none()
    {
        // When we are at a module scope (as checked above) the eval contains
        // references to all values, so walking covers everything and the unsafe
        // is satisfied.
        unsafe {
            eval.garbage_collect()
        }
        eval.next_gc_level = eval.heap().allocated_bytes() + GC_THRESHOLD;
    }
}

/// Implement lhs += rhs, which is special in Starlark, because lists are mutated,
/// while all other types are not.
fn add_assign<'v>(lhs: Value<'v>, rhs: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
    // Addition of strings is super common, so have a special case
    if let Some(ls) = lhs.unpack_str() {
        if let Some(rs) = rhs.unpack_str() {
            if ls.is_empty() {
                return Ok(rhs);
            } else if rs.is_empty() {
                return Ok(lhs);
            } else {
                return Ok(heap.alloc_str_concat(ls, rs));
            }
        }
    }

    // The Starlark spec says list += mutates, while nothing else does.
    // When mutating, be careful if they alias, so we don't have `lhs`
    // mutably borrowed when we iterate over `rhs`, as they might alias.

    // In practice, select is the only thing that implements radd.
    // If the users does x += select(...) we don't want an error,
    // we really want to x = x + select, so check radd first.
    if let Some(v) = rhs.get_ref().radd(lhs, heap) {
        v
    } else {
        let lhs_aref = lhs.get_ref();
        let lhs_ty = lhs_aref.static_type_of_value();

        if List::is_list_type(lhs_ty) {
            // If the value is None, that must mean its a FrozenList, thus turn it into an immutable error
            let mut list = List::from_value_mut(lhs)?
                .ok_or_else(|| anyhow!(ValueError::CannotMutateImmutableValue))?;
            if lhs.ptr_eq(rhs) {
                list.content.extend_from_within(..);
            } else {
                rhs.with_iterator(heap, |it| list.content.extend(it))?;
            }
            Ok(lhs)
        } else {
            lhs_aref.add(rhs, heap)
        }
    }
}

impl Compiler<'_> {
    pub(crate) fn compile_context(&self) -> StmtCompileContext {
        StmtCompileContext {
            has_before_stmt: self.has_before_stmt,
        }
    }

    pub(crate) fn stmt(&mut self, stmt: CstStmt, allow_gc: bool) -> StmtsCompiled {
        let span = stmt.span;
        let is_statements = matches!(&stmt.node, StmtP::Statements(_));
        let res = self.stmt_direct(stmt, allow_gc);
        // No point inserting a GC point around statements, since they will contain inner statements we can do
        if allow_gc && !is_statements {
            // We could do this more efficiently by fusing the possible_gc
            // into the inner closure, but no real need - we insert allow_gc fairly rarely
            let mut with_gc = StmtsCompiled::one(Spanned {
                span,
                node: StmtCompiledValue::PossibleGc,
            });
            with_gc.extend(res);
            with_gc
        } else {
            res
        }
    }

    fn stmt_if(
        &mut self,
        span: Span,
        cond: CstExpr,
        then_block: CstStmt,
        allow_gc: bool,
    ) -> StmtsCompiled {
        let cond = self.expr(cond);
        let then_block = self.stmt(then_block, allow_gc);
        <Spanned<StmtCompiledValue>>::if_stmt(span, cond, then_block, StmtsCompiled::empty())
    }

    fn stmt_if_else(
        &mut self,
        span: Span,
        cond: CstExpr,
        then_block: CstStmt,
        else_block: CstStmt,
        allow_gc: bool,
    ) -> StmtsCompiled {
        let cond = self.expr(cond);
        let then_block = self.stmt(then_block, allow_gc);
        let else_block = self.stmt(else_block, allow_gc);
        <Spanned<StmtCompiledValue>>::if_stmt(span, cond, then_block, else_block)
    }

    fn stmt_expr(&mut self, expr: CstExpr) -> StmtsCompiled {
        let expr = self.expr(expr);
        <Spanned<StmtCompiledValue>>::expr(expr)
    }

    fn stmt_direct(&mut self, stmt: CstStmt, allow_gc: bool) -> StmtsCompiled {
        let span = stmt.span;
        match stmt.node {
            StmtP::Def(name, params, return_type, suite, scope_id) => {
                let rhs = Spanned {
                    node: self.function(&name.0, scope_id, params, return_type, *suite),
                    span,
                };
                let lhs = self.assign(Spanned {
                    span: name.span,
                    node: AssignP::Identifier(name),
                });
                StmtsCompiled::one(Spanned {
                    span,
                    node: StmtCompiledValue::Assign(lhs, rhs),
                })
            }
            StmtP::For(var, box (over, body)) => {
                let over = list_to_tuple(over);
                let var = self.assign(var);
                let over = self.expr(over);
                let st = self.stmt(body, false);
                StmtsCompiled::one(Spanned {
                    span,
                    node: StmtCompiledValue::For(box (var, over, st)),
                })
            }
            StmtP::Return(e) => StmtsCompiled::one(Spanned {
                node: StmtCompiledValue::Return(e.map(|e| self.expr(e))),
                span,
            }),
            StmtP::If(cond, box then_block) => self.stmt_if(span, cond, then_block, allow_gc),
            StmtP::IfElse(cond, box (then_block, else_block)) => {
                self.stmt_if_else(span, cond, then_block, else_block, allow_gc)
            }
            StmtP::Statements(stmts) => {
                let mut r = StmtsCompiled::empty();
                for stmt in stmts {
                    r.extend(self.stmt(stmt, allow_gc));
                }
                r
            }
            StmtP::Expression(e) => self.stmt_expr(e),
            StmtP::Assign(lhs, rhs) => {
                let rhs = self.expr(*rhs);
                let lhs = self.assign(lhs);
                StmtsCompiled::one(Spanned {
                    span,
                    node: StmtCompiledValue::Assign(lhs, rhs),
                })
            }
            StmtP::AssignModify(lhs, op, rhs) => {
                let rhs = self.expr(*rhs);
                self.assign_modify(span, lhs, rhs, op)
            }
            StmtP::Load(..) => unreachable!(),
            StmtP::Pass => StmtsCompiled::empty(),
            StmtP::Break => StmtsCompiled::one(Spanned {
                span,
                node: StmtCompiledValue::Break,
            }),
            StmtP::Continue => StmtsCompiled::one(Spanned {
                span,
                node: StmtCompiledValue::Continue,
            }),
        }
    }
}
