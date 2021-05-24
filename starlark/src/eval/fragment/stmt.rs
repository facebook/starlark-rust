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
        compiler::{scope::Slot, thrw, Compiler, EvalException, ExprCompiled, StmtCompiled},
        runtime::evaluator::Evaluator,
    },
    syntax::ast::{Assign, AssignOp, AstAssign, AstStmt, Expr, Stmt, Visibility},
    values::{
        fast_string,
        list::{FrozenList, List},
        ControlError, Heap, Value,
    },
};
use gazebo::prelude::*;
use std::{collections::HashMap, mem};
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
    let nvl = thrw(value.length(), span, eval)?;
    if nvl != l {
        thrw(
            Err(AssignError::IncorrectNumberOfValueToUnpack(l, nvl).into()),
            span,
            eval,
        )
    } else {
        let mut it1 = lvalues.iter();
        // TODO: the span here should probably include the rvalue
        let it2 = thrw(value.iterate(eval.heap()), span, eval)?;
        let mut it2 = it2.iter();
        for _ in 0..l {
            it1.next().unwrap()(it2.next().unwrap(), eval)?;
        }
        Ok(())
    }
}

impl Compiler<'_> {
    pub fn assign(&mut self, expr: AstAssign) -> AssignCompiled {
        let span = expr.span;
        match expr.node {
            Assign::Dot(e, s) => {
                let e = self.expr(*e);
                let s = s.node;
                box move |value, eval| thrw(e(eval)?.set_attr(&s, value, eval.heap()), span, eval)
            }
            Assign::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e);
                let idx = self.expr(idx);
                box move |value, eval| {
                    thrw(e(eval)?.set_at(idx(eval)?, value, eval.heap()), span, eval)
                }
            }
            Assign::Tuple(v) => {
                let v = v.into_map(|x| self.assign(x));
                box move |value, eval| eval_assign_list(&v, span, value, eval)
            }
            Assign::Identifier(ident) => match self.scope.get_name_or_panic(&ident.node) {
                Slot::Local(slot) => box move |value, eval| {
                    eval.set_slot_local(slot, value);
                    Ok(())
                },
                Slot::Module(slot) => box move |value, eval| {
                    // Make sure that `ComplexValue`s get their name as soon as possible
                    value.export_as(&ident.node, eval.heap());
                    eval.set_slot_module(slot, value);
                    Ok(())
                },
            },
        }
    }

    fn assign_modify(
        &mut self,
        span_stmt: Span,
        lhs: AstAssign,
        rhs: ExprCompiled,
        op: for<'v> fn(Value<'v>, Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>>,
    ) -> StmtCompiled {
        let span_lhs = lhs.span;
        match lhs.node {
            Assign::Dot(e, s) => {
                let e = self.expr(*e);
                let s = s.node;
                box move |eval| {
                    before_stmt(span_stmt, eval);
                    let e: Value = e(eval)?;
                    let (_, v) = thrw(e.get_attr(&s, eval.heap()), span_lhs, eval)?;
                    let rhs = rhs(eval)?;
                    thrw(
                        e.set_attr(&s, thrw(op(v, rhs, eval), span_stmt, eval)?, eval.heap()),
                        span_stmt,
                        eval,
                    )?;
                    Ok(())
                }
            }
            Assign::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e);
                let idx = self.expr(idx);
                box move |eval| {
                    before_stmt(span_stmt, eval);
                    let e: Value = e(eval)?;
                    let idx = idx(eval)?;
                    let v = thrw(e.at(idx, eval.heap()), span_lhs, eval)?;
                    let rhs = rhs(eval)?;
                    thrw(
                        e.set_at(idx, thrw(op(v, rhs, eval), span_stmt, eval)?, eval.heap()),
                        span_stmt,
                        eval,
                    )?;
                    Ok(())
                }
            }
            Assign::Identifier(ident) => {
                let name = ident.node;
                match self.scope.get_name_or_panic(&name) {
                    Slot::Local(slot) => box move |eval| {
                        before_stmt(span_stmt, eval);
                        let v = thrw(eval.get_slot_local(slot, &name), span_lhs, eval)?;
                        let rhs = rhs(eval)?;
                        let v = thrw(op(v, rhs, eval), span_stmt, eval)?;
                        eval.set_slot_local(slot, v);
                        Ok(())
                    },
                    Slot::Module(slot) => box move |eval| {
                        before_stmt(span_stmt, eval);
                        let v = thrw(eval.get_slot_module(slot), span_lhs, eval)?;
                        let rhs = rhs(eval)?;
                        let v = thrw(op(v, rhs, eval), span_stmt, eval)?;
                        eval.set_slot_module(slot, v);
                        Ok(())
                    },
                }
            }
            Assign::Tuple(_) => {
                unreachable!("Assign modify validates that the LHS is never a tuple")
            }
        }
    }
}

// This function should be called before every meaningful statement.
// The purposes are GC, profiling and debugging.
fn before_stmt(span: Span, eval: &mut Evaluator) {
    // Almost always will be empty, especially in high-perf use cases
    if !eval.before_stmt.is_empty() {
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
    // We only actually GC if there have been GC_THRESHOLD bytes allocated since the
    // last time we GC'd
    const GC_THRESHOLD: usize = 100000;

    if !eval.disable_gc
        && eval.heap().allocated_bytes() >= eval.last_heap_size + GC_THRESHOLD
        && eval.extra_v.is_none()
    {
        // When we are at a module scope (as checked above) the eval contains
        // references to all values, so walking covers everything and the unsafe
        // is satisfied.
        unsafe {
            eval.heap().garbage_collect(|walker| eval.walk(walker))
        }
        eval.last_heap_size = eval.heap().allocated_bytes();
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
                return Ok(heap.alloc(fast_string::append(ls, rs)));
            }
        }
    }

    // The Starlark spec says list += mutates, while nothing else does.
    // When mutating, be careful we collect first, so we don't have `lhs`
    // mutably borrowed when we iterate over `rhs`, as they might alias.
    // We also have to carefully prod frozen lists, in case they are
    // copy-on-write.
    if lhs.downcast_ref::<List>().is_some() || lhs.downcast_ref::<FrozenList>().is_some() {
        let xs = rhs.iterate_collect(heap)?;
        match List::from_value_mut(lhs, heap)? {
            None => Err(ControlError::CannotMutateImmutableValue.into()),
            Some(mut list) => {
                list.extend(xs);
                Ok(lhs)
            }
        }
    } else {
        Value::add(lhs, rhs, heap)
    }
}

impl Stmt {
    // Collect all the variables that are defined in this scope
    pub(crate) fn collect_defines<'a>(
        stmt: &'a AstStmt,
        result: &mut HashMap<&'a str, Visibility>,
    ) {
        match &stmt.node {
            Stmt::Assign(dest, _) | Stmt::AssignModify(dest, _, _) => {
                Expr::collect_defines_lvalue(dest, result);
            }
            Stmt::For(dest, box (_, body)) => {
                Expr::collect_defines_lvalue(dest, result);
                Stmt::collect_defines(body, result);
            }
            Stmt::Def(name, ..) => {
                result.insert(&name.node, Visibility::Public);
            }
            Stmt::Load(_, names, vis) => {
                for (name, _) in names {
                    // If we are in the map as Public and Private, then Public wins.
                    // Everything but Load is definitely Public.
                    // So only insert if it wasn't already there.
                    result.entry(&name.node).or_insert(*vis);
                }
            }
            _ => stmt.node.visit_stmt(|x| Stmt::collect_defines(x, result)),
        }
    }

    fn flatten_statements(xs: Vec<AstStmt>) -> Vec<AstStmt> {
        let mut res = Vec::with_capacity(xs.len());
        for x in xs.into_iter() {
            match x.node {
                Stmt::Statements(x) => res.extend(Stmt::flatten_statements(x)),
                _ => res.push(x),
            }
        }
        res
    }
}

impl Compiler<'_> {
    pub(crate) fn stmt(&mut self, stmt: AstStmt, allow_gc: bool) -> StmtCompiled {
        let is_statements = matches!(&stmt.node, Stmt::Statements(_));
        let res = self.stmt_direct(stmt, allow_gc);
        // No point inserting a GC point around statements, since they will contain inner statements we can do
        if allow_gc && is_statements {
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

    fn stmt_direct(&mut self, stmt: AstStmt, allow_gc: bool) -> StmtCompiled {
        let span = stmt.span;
        match stmt.node {
            Stmt::Def(name, params, return_type, suite) => {
                let rhs = self.function(&name.node, params, return_type, *suite);
                let lhs = self.assign(Spanned {
                    span: name.span,
                    node: Assign::Identifier(name),
                });
                box move |eval| {
                    before_stmt(span, eval);
                    lhs(rhs(eval)?, eval)?;
                    Ok(())
                }
            }
            Stmt::For(var, box (over, body)) => {
                let over_span = over.span;
                let var = self.assign(var);
                let over = self.expr(over);
                let st = self.stmt(body, false);
                box move |eval| {
                    before_stmt(span, eval);
                    let iterable = over(eval)?;
                    let freeze_for_iteration = iterable.get_aref();
                    for v in &thrw(iterable.iterate(eval.heap()), over_span, eval)? {
                        var(v, eval)?;
                        match st(eval) {
                            Err(EvalException::Break) => break,
                            Err(EvalException::Continue) => {}
                            Err(e) => return Err(e),
                            _ => {}
                        }
                    }
                    mem::drop(freeze_for_iteration);
                    Ok(())
                }
            }
            Stmt::Return(Some(e)) => {
                let e = self.expr(e);
                box move |eval| {
                    before_stmt(span, eval);
                    Err(EvalException::Return(e(eval)?))
                }
            }
            Stmt::Return(None) => box move |eval| {
                before_stmt(span, eval);
                Err(EvalException::Return(Value::new_none()))
            },
            Stmt::If(cond, box then_block) => {
                let cond = self.expr(cond);
                let then_block = self.stmt(then_block, allow_gc);
                box move |eval| {
                    before_stmt(span, eval);
                    if cond(eval)?.to_bool() {
                        then_block(eval)
                    } else {
                        Ok(())
                    }
                }
            }
            Stmt::IfElse(cond, box (then_block, else_block)) => {
                let cond = self.expr(cond);
                let then_block = self.stmt(then_block, allow_gc);
                let else_block = self.stmt(else_block, allow_gc);
                box move |eval| {
                    before_stmt(span, eval);
                    if cond(eval)?.to_bool() {
                        then_block(eval)
                    } else {
                        else_block(eval)
                    }
                }
            }
            Stmt::Statements(stmts) => {
                // No need to do before_stmt on these statements as they are
                // not meaningful statements
                let stmts = Stmt::flatten_statements(stmts);
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
            Stmt::Expression(e) => {
                let e = self.expr(e);
                box move |eval| {
                    before_stmt(span, eval);
                    e(eval)?;
                    Ok(())
                }
            }
            Stmt::Assign(lhs, rhs) => {
                let rhs = self.expr(*rhs);
                let lhs = self.assign(lhs);
                box move |eval| {
                    before_stmt(span, eval);
                    lhs(rhs(eval)?, eval)?;
                    Ok(())
                }
            }
            Stmt::AssignModify(lhs, op, rhs) => {
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
            Stmt::Load(name, v, _) => {
                let name = name.node;
                let symbols = v.into_map(|(x, y)| {
                    (
                        self.scope.get_name_or_panic(&x.node),
                        y.node,
                        x.span.merge(y.span),
                    )
                });
                box move |eval| {
                    before_stmt(span, eval);
                    let loadenv = match eval.loader.as_mut() {
                        None => {
                            return Err(EvalException::Error(
                                EnvironmentError::NoImportsAvailable(name.to_owned()).into(),
                            ));
                        }
                        Some(load) => load.load(&name).map_err(EvalException::Error)?,
                    };
                    for (new_name, orig_name, span) in &symbols {
                        let value = thrw(
                            eval.module_env.load_symbol(&loadenv, orig_name),
                            *span,
                            eval,
                        )?;
                        match new_name {
                            Slot::Local(slot) => eval.set_slot_local(*slot, value),
                            Slot::Module(slot) => eval.set_slot_module(*slot, value),
                        }
                    }
                    Ok(())
                }
            }
            Stmt::Pass => box move |eval| {
                before_stmt(span, eval);
                Ok(())
            },
            Stmt::Break => box move |eval| {
                before_stmt(span, eval);
                Err(EvalException::Break)
            },
            Stmt::Continue => box move |eval| {
                before_stmt(span, eval);
                Err(EvalException::Continue)
            },
        }
    }
}
