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
    environment::EnvironmentError,
    eval::{
        compiler::{
            scope::{CstAssign, CstStmt, Slot},
            throw, Compiler, EvalException, ExprCompiledValue, StmtCompiled,
        },
        fragment::known::{list_to_tuple, Conditional},
        runtime::evaluator::{Evaluator, GC_THRESHOLD},
    },
    syntax::ast::{AssignOp, AssignP, AstPayload, AstStmtP, ExprP, StmtP},
    values::{list::List, Heap, Trace, Value, ValueError},
};
use anyhow::anyhow;
use gazebo::prelude::*;
use std::mem;
use thiserror::Error;

#[derive(Debug, Error)]
enum AssignError {
    // Incorrect number of value to unpack (expected, got)
    #[error("Unpacked {1} values but expected {0}")]
    IncorrectNumberOfValueToUnpack(i32, i32),
}

pub(crate) type AssignCompiled = Box<
    dyn for<'v> Fn(Value<'v>, &mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>>
        + Send
        + Sync,
>;

fn eval_assign_list<'v>(
    lvalues: &[AssignCompiled],
    span: Span,
    value: Value<'v>,
    eval: &mut Evaluator<'v, '_>,
) -> Result<(), EvalException<'v>> {
    let l = lvalues.len() as i32;
    let nvl = throw(value.length(), span, eval)?;
    if nvl != l {
        throw(
            Err(AssignError::IncorrectNumberOfValueToUnpack(l, nvl).into()),
            span,
            eval,
        )
    } else {
        let mut it1 = lvalues.iter();
        // TODO: the span here should probably include the rvalue
        let mut it2 = throw(value.iterate(eval.heap()), span, eval)?;
        for _ in 0..l {
            it1.next().unwrap()(it2.next().unwrap(), eval)?;
        }
        Ok(())
    }
}

impl Compiler<'_> {
    pub fn assign(&mut self, expr: CstAssign) -> AssignCompiled {
        let span = expr.span;
        match expr.node {
            AssignP::Dot(e, s) => {
                let e = self.expr(*e).as_compiled();
                let s = s.node;
                box move |value, eval| throw(e(eval)?.set_attr(&s, value), span, eval)
            }
            AssignP::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e).as_compiled();
                let idx = self.expr(idx).as_compiled();
                box move |value, eval| throw(e(eval)?.set_at(idx(eval)?, value), span, eval)
            }
            AssignP::Tuple(v) => {
                let v = v.into_map(|x| self.assign(x));
                box move |value, eval| eval_assign_list(&v, span, value, eval)
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
                match slot {
                    Slot::Local(slot) => box move |value, eval| {
                        eval.set_slot_local(slot, value);
                        Ok(())
                    },
                    Slot::Module(slot) => box move |value, eval| {
                        // Make sure that `ComplexValue`s get their name as soon as possible
                        value.export_as(&name, eval);
                        eval.set_slot_module(slot, value);
                        Ok(())
                    },
                }
            }
        }
    }

    fn assign_modify(
        &mut self,
        span_stmt: Span,
        lhs: CstAssign,
        rhs: ExprCompiledValue,
        op: for<'v> fn(Value<'v>, Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>>,
    ) -> StmtCompiled {
        let span_lhs = lhs.span;
        match lhs.node {
            AssignP::Dot(e, s) => {
                let e = self.expr(*e).as_compiled();
                let s = s.node;
                let rhs = rhs.as_compiled();
                stmt!("assign_dot", span_stmt, |eval| {
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
            AssignP::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e).as_compiled();
                let idx = self.expr(idx).as_compiled();
                let rhs = rhs.as_compiled();
                stmt!("assign_array", span_stmt, |eval| {
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
            AssignP::Identifier(ident) => {
                let slot = self.scope_data.get_assign_ident_slot(&ident);
                let name = ident.node;
                match slot {
                    Slot::Local(slot) => {
                        let rhs = rhs.as_compiled();
                        let name = name.0;
                        stmt!("assign_local", span_stmt, |eval| {
                            let v = throw(eval.get_slot_local(slot, &name), span_lhs, eval)?;
                            let rhs = rhs(eval)?;
                            let v = throw(op(v, rhs, eval), span_stmt, eval)?;
                            eval.set_slot_local(slot, v);
                        })
                    }
                    Slot::Module(slot) => {
                        let rhs = rhs.as_compiled();
                        stmt!("assign_module", span_stmt, |eval| {
                            let v = throw(eval.get_slot_module(slot), span_lhs, eval)?;
                            let rhs = rhs(eval)?;
                            let v = throw(op(v, rhs, eval), span_stmt, eval)?;
                            eval.set_slot_module(slot, v);
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
fn before_stmt(span: Span, eval: &mut Evaluator) {
    // In all the high-performance use cases we don't have any `before_stmt` things set,
    // so ensure the check gets inlined but the operation doesn't.
    #[inline(never)]
    fn have_stmt(span: Span, eval: &mut Evaluator) {
        // The user could inject more before_stmt values during iteration (although that sounds like a bad plan!)
        // so grab the values at the start, and add any additional at the end.
        let fs = mem::take(&mut eval.before_stmt);
        for f in &fs {
            f(span, eval)
        }
        let added = mem::replace(&mut eval.before_stmt, fs);
        for x in added {
            eval.before_stmt.push(x)
        }
    }

    // Almost always will be empty, especially in high-perf use cases
    if !eval.before_stmt.is_empty() {
        have_stmt(span, eval)
    }
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
        eval.ann("garbage_collection", |eval| {
            // When we are at a module scope (as checked above) the eval contains
            // references to all values, so walking covers everything and the unsafe
            // is satisfied.
            unsafe {
                eval.heap().garbage_collect(|tracer| eval.trace(tracer))
            }
            eval.next_gc_level = eval.heap().allocated_bytes() + GC_THRESHOLD;
        })
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

    let lhs_aref = lhs.get_ref();
    let lhs_ty = lhs_aref.static_type_of();

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
    } else if let Some(v) = rhs.get_ref().radd(lhs, heap) {
        v
    } else {
        lhs_aref.add(rhs, heap)
    }
}

impl<P: AstPayload> StmtP<P> {
    // Return statements to execute, skipping those that have no effect
    // and flattening any nested Statements
    fn flatten_statements(xs: Vec<AstStmtP<P>>) -> Vec<AstStmtP<P>> {
        fn has_effect<P: AstPayload>(x: &ExprP<P>) -> bool {
            match x {
                ExprP::Literal(_) => false,
                _ => true,
            }
        }

        let mut res = Vec::with_capacity(xs.len());
        for x in xs.into_iter() {
            match x.node {
                StmtP::Statements(x) => res.extend(StmtP::flatten_statements(x)),
                StmtP::Pass => {}
                StmtP::Expression(x) if !has_effect(&x) => {}
                _ => res.push(x),
            }
        }
        res
    }
}

impl Compiler<'_> {
    pub(crate) fn stmt(&mut self, stmt: CstStmt, allow_gc: bool) -> StmtCompiled {
        let is_statements = matches!(&stmt.node, StmtP::Statements(_));
        let res = self.stmt_direct(stmt, allow_gc);
        // No point inserting a GC point around statements, since they will contain inner statements we can do
        if allow_gc && !is_statements {
            // We could do this more efficiently by fusing the possible_gc
            // into the inner closure, but no real need - we insert allow_gc fairly rarely
            box move |eval| {
                possible_gc(eval);
                res(eval)
            }
        } else {
            res
        }
    }

    fn stmt_direct(&mut self, stmt: CstStmt, allow_gc: bool) -> StmtCompiled {
        let span = stmt.span;
        match stmt.node {
            StmtP::Def(name, params, return_type, suite, scope_id) => {
                let rhs = self
                    .function(&name.0, scope_id, params, return_type, *suite)
                    .as_compiled();
                let lhs = self.assign(Spanned {
                    span: name.span,
                    node: AssignP::Identifier(name),
                });
                stmt!("define_def", span, |eval| {
                    lhs(rhs(eval)?, eval)?;
                })
            }
            StmtP::For(var, box (over, body)) => {
                let over = list_to_tuple(over);
                let over_span = over.span;
                let var = self.assign(var);
                let over = self.expr(over).as_compiled();
                let st = self.stmt(body, false);
                stmt!("for", span, |eval| {
                    let heap = eval.heap();
                    let iterable = over(eval)?;
                    throw(
                        iterable.with_iterator(heap, |it| {
                            for v in it {
                                match var(v, eval).and_then(|_| st(eval)) {
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
            StmtP::Return(Some(e)) => {
                let e = self.expr(e).as_compiled();
                stmt!("return_value", span, |eval| {
                    return Err(EvalException::Return(e(eval)?));
                })
            }
            StmtP::Return(None) => stmt!("return", span, |eval| {
                return Err(EvalException::Return(Value::new_none()));
            }),
            StmtP::If(cond, box then_block) => {
                let then_block = self.stmt(then_block, allow_gc);
                match self.conditional(cond) {
                    Conditional::True => then_block,
                    Conditional::False => stmt!("if_false", span, |eval| {}),
                    Conditional::Normal(cond) => {
                        stmt!("if_then", span, |eval| if cond(eval)?.to_bool() {
                            then_block(eval)?
                        })
                    }
                    Conditional::Negate(cond) => {
                        stmt!("if_then", span, |eval| if !cond(eval)?.to_bool() {
                            then_block(eval)?
                        })
                    }
                }
            }
            StmtP::IfElse(cond, box (then_block, else_block)) => {
                let then_block = self.stmt(then_block, allow_gc);
                let else_block = self.stmt(else_block, allow_gc);
                let (cond, t, f) = match self.conditional(cond) {
                    Conditional::True => return then_block,
                    Conditional::False => return else_block,
                    Conditional::Normal(cond) => (cond, then_block, else_block),
                    Conditional::Negate(cond) => (cond, else_block, then_block),
                };
                stmt!("if_then_else", span, |eval| if cond(eval)?.to_bool() {
                    t(eval)?
                } else {
                    f(eval)?
                })
            }
            StmtP::Statements(stmts) => {
                // No need to do before_stmt on these statements as they are
                // not meaningful statements
                let stmts = StmtP::flatten_statements(stmts);
                let mut stmts = stmts.into_map(|x| self.stmt(x, allow_gc));
                match stmts.len() {
                    0 => box move |_| Ok(()),
                    1 => stmts.pop().unwrap(),
                    _ => box move |eval| {
                        for stmt in &stmts {
                            stmt(eval)?;
                        }
                        Ok(())
                    },
                }
            }
            StmtP::Expression(e) => {
                let e = self.expr(e).as_compiled();
                stmt!("expression", span, |eval| {
                    e(eval)?;
                })
            }
            StmtP::Assign(lhs, rhs) => {
                let rhs = self.expr(*rhs).as_compiled();
                let lhs = self.assign(lhs);
                stmt!("assign", span, |eval| {
                    lhs(rhs(eval)?, eval)?;
                })
            }
            StmtP::AssignModify(lhs, op, rhs) => {
                let rhs = self.expr(*rhs);
                match op {
                    AssignOp::Add => self
                        .assign_modify(span, lhs, rhs, |l, r, eval| add_assign(l, r, eval.heap())),
                    AssignOp::Subtract => {
                        self.assign_modify(span, lhs, rhs, |l, r, eval| l.sub(r, eval.heap()))
                    }
                    AssignOp::Multiply => {
                        self.assign_modify(span, lhs, rhs, |l, r, eval| l.mul(r, eval.heap()))
                    }
                    AssignOp::FloorDivide => {
                        self.assign_modify(span, lhs, rhs, |l, r, eval| l.floor_div(r, eval.heap()))
                    }
                    AssignOp::Percent => {
                        self.assign_modify(span, lhs, rhs, |l, r, eval| l.percent(r, eval.heap()))
                    }
                    AssignOp::BitAnd => self.assign_modify(span, lhs, rhs, |l, r, _| l.bit_and(r)),
                    AssignOp::BitOr => self.assign_modify(span, lhs, rhs, |l, r, _| l.bit_or(r)),
                    AssignOp::BitXor => self.assign_modify(span, lhs, rhs, |l, r, _| l.bit_xor(r)),
                    AssignOp::LeftShift => {
                        self.assign_modify(span, lhs, rhs, |l, r, _| l.left_shift(r))
                    }
                    AssignOp::RightShift => {
                        self.assign_modify(span, lhs, rhs, |l, r, _| l.right_shift(r))
                    }
                }
            }
            StmtP::Load(load) => {
                let name = load.node.module.node;
                let symbols = load.node.args.into_map(|(x, y)| {
                    let slot = self.scope_data.get_assign_ident_slot(&x);
                    (
                        match slot {
                            Slot::Local(..) => unreachable!("symbol need to be resolved to module"),
                            Slot::Module(slot) => slot,
                        },
                        y.node,
                        x.span.merge(y.span),
                    )
                });
                stmt!("load", span, |eval| {
                    let loadenv = match eval.loader.as_ref() {
                        None => {
                            return Err(EvalException::Error(
                                EnvironmentError::NoImportsAvailable(name.to_owned()).into(),
                            ));
                        }
                        Some(load) => load.load(&name).map_err(EvalException::Error)?,
                    };
                    for (new_name, orig_name, span) in &symbols {
                        let value = throw(
                            eval.module_env.load_symbol(&loadenv, orig_name),
                            *span,
                            eval,
                        )?;
                        eval.set_slot_module(*new_name, value)
                    }
                })
            }
            StmtP::Pass => stmt!("pass", span, |eval| {}),
            StmtP::Break => stmt!("break", span, |eval| return Err(EvalException::Break)),
            StmtP::Continue => stmt!("continue", span, |eval| return Err(EvalException::Continue)),
        }
    }
}
