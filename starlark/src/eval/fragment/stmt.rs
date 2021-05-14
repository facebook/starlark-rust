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
        compiler::{scope::Slot, thrw, Compiler, EvalException, ExprCompiled},
        runtime::evaluator::Evaluator,
    },
    syntax::ast::{AssignOp, AstExpr, AstStmt, Expr, Stmt, Visibility},
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
    // Expression used as left value cannot be assigned
    #[error("Incorrect expression as left value")]
    IncorrectLeftValue,
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
    context: &mut Evaluator<'v, '_>,
) -> Result<(), EvalException<'v>> {
    let l = lvalues.len() as i32;
    let nvl = thrw(value.length(), span, context)?;
    if nvl != l {
        thrw(
            Err(AssignError::IncorrectNumberOfValueToUnpack(l, nvl).into()),
            span,
            context,
        )
    } else {
        let mut it1 = lvalues.iter();
        // TODO: the span here should probably include the rvalue
        let it2 = thrw(value.iterate(context.heap()), span, context)?;
        let mut it2 = it2.iter();
        for _ in 0..l {
            it1.next().unwrap()(it2.next().unwrap(), context)?;
        }
        Ok(())
    }
}

impl Compiler<'_> {
    pub fn assign(&mut self, expr: AstExpr) -> AssignCompiled {
        let span = expr.span;
        match expr.node {
            Expr::Dot(e, s) => {
                let e = self.expr(*e);
                let s = s.node;
                box move |value, context| {
                    thrw(
                        e(context)?.set_attr(&s, value, context.heap()),
                        span,
                        context,
                    )
                }
            }
            Expr::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e);
                let idx = self.expr(idx);
                box move |value, context| {
                    thrw(
                        e(context)?.set_at(idx(context)?, value, context.heap()),
                        span,
                        context,
                    )
                }
            }
            Expr::Tuple(v) | Expr::List(v) => {
                let v = v.into_map(|x| self.assign(x));
                box move |value, context| eval_assign_list(&v, span, value, context)
            }
            Expr::Identifier(ident) => match self.scope.get_name_or_panic(&ident.node) {
                Slot::Local(slot) => box move |value, context| {
                    context.set_slot_local(slot, value);
                    Ok(())
                },
                Slot::Module(slot) => box move |value, context| {
                    // Make sure that `ComplexValue`s get their name as soon as possible
                    value.export_as(&ident.node, context.heap());
                    context.set_slot_module(slot, value);
                    Ok(())
                },
            },
            _ => box move |_, context| {
                thrw(Err(AssignError::IncorrectLeftValue.into()), span, context)
            },
        }
    }

    fn assign_modify(
        &mut self,
        span_op: Span,
        lhs: AstExpr,
        rhs: ExprCompiled,
        op: for<'v> fn(Value<'v>, Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>>,
    ) -> ExprCompiled {
        let span = lhs.span;
        match lhs.node {
            Expr::Dot(e, s) => {
                let e = self.expr(*e);
                let s = s.node;
                box move |context| {
                    before_stmt(span, context);
                    let e: Value = e(context)?;
                    let (_, v) = thrw(e.get_attr(&s, context.heap()), span, context)?;
                    let rhs = rhs(context)?;
                    thrw(
                        e.set_attr(
                            &s,
                            thrw(op(v, rhs, context), span_op, context)?,
                            context.heap(),
                        ),
                        span,
                        context,
                    )?;
                    Ok(Value::new_none())
                }
            }
            Expr::ArrayIndirection(box (e, idx)) => {
                let e = self.expr(e);
                let idx = self.expr(idx);
                box move |context| {
                    before_stmt(span, context);
                    let e: Value = e(context)?;
                    let idx = idx(context)?;
                    let v = thrw(e.at(idx, context.heap()), span, context)?;
                    let rhs = rhs(context)?;
                    thrw(
                        e.set_at(
                            idx,
                            thrw(op(v, rhs, context), span_op, context)?,
                            context.heap(),
                        ),
                        span,
                        context,
                    )?;
                    Ok(Value::new_none())
                }
            }
            Expr::Identifier(ident) => {
                let name = ident.node;
                match self.scope.get_name_or_panic(&name) {
                    Slot::Local(slot) => box move |context| {
                        before_stmt(span, context);
                        let v = thrw(context.get_slot_local(slot, &name), span, context)?;
                        let rhs = rhs(context)?;
                        let v = thrw(op(v, rhs, context), span_op, context)?;
                        context.set_slot_local(slot, v);
                        Ok(Value::new_none())
                    },
                    Slot::Module(slot) => box move |context| {
                        before_stmt(span, context);
                        let v = thrw(context.get_slot_module(slot), span, context)?;
                        let rhs = rhs(context)?;
                        let v = thrw(op(v, rhs, context), span_op, context)?;
                        context.set_slot_module(slot, v);
                        Ok(Value::new_none())
                    },
                }
            }
            _ => box move |context| {
                before_stmt(span, context);
                thrw(Err(AssignError::IncorrectLeftValue.into()), span, context)
            },
        }
    }
}

// This function should be called before every meaningful statement.
// The purposes are GC, profiling and debugging.
//
// There are two requirements to perform a GC:
//
// 1. We can't be profiling, since profiling relies on the redundant heap
//    entries. When profiling we set disable_gc.
// 2. We must be able to access all roots.
//
// We track as many roots as possible, and eventually aim to track them all, but
// for the moment we're only sure we have all roots when we are in the module
// evaluation context. There are three roots we don't yet know about:
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
fn before_stmt(span: Span, context: &mut Evaluator) {
    // Almost always will be empty, especially in high-perf use cases
    if !context.before_stmt.is_empty() {
        // The user could inject more before_stmt values during iteration (although that sounds like a bad plan!)
        // so grab the values at the start, and add any additional at the end.
        let fs = mem::take(&mut context.before_stmt);
        for f in &fs {
            f(span, context)
        }
        let added = mem::replace(&mut context.before_stmt, fs);
        for x in added {
            context.before_stmt.push(x)
        }
    }

    // We only actually GC if there have been GC_THRESHOLD bytes allocated since the
    // last time we GC'd
    const GC_THRESHOLD: usize = 100000;

    if context.is_module_scope
        && !context.disable_gc
        && context.heap().allocated_bytes() >= context.last_heap_size + GC_THRESHOLD
        && context.extra_v.is_none()
    {
        // When we are at a module scope (as checked above) the context contains
        // references to all values, so walking covers everything and the unsafe
        // is satisfied.
        unsafe {
            context
                .heap()
                .garbage_collect(|walker| context.walk(walker))
        }
        context.last_heap_size = context.heap().allocated_bytes();
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
            Stmt::Assign(dest, _, _) => {
                Expr::collect_defines_lvalue(dest, result);
            }
            Stmt::For(box (dest, _, body)) => {
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
    pub(crate) fn stmt(&mut self, stmt: AstStmt) -> ExprCompiled {
        let span = stmt.span;
        match stmt.node {
            Stmt::Def(name, params, return_type, suite) => {
                let rhs = self.function(&name.node, params, return_type, *suite);
                let lhs = self.assign(Spanned {
                    span: name.span,
                    node: Expr::Identifier(name),
                });
                box move |context| {
                    before_stmt(span, context);
                    lhs(rhs(context)?, context)?;
                    Ok(Value::new_none())
                }
            }
            Stmt::For(box (var, over, body)) => {
                let over_span = over.span;
                let var = self.assign(var);
                let over = self.expr(over);
                let st = self.stmt(body);
                box move |context| {
                    before_stmt(span, context);
                    let iterable = over(context)?;
                    let freeze_for_iteration = iterable.get_aref();
                    for v in &thrw(iterable.iterate(context.heap()), over_span, context)? {
                        var(v, context)?;
                        match st(context) {
                            Err(EvalException::Break) => break,
                            Err(EvalException::Continue) => {}
                            Err(e) => return Err(e),
                            _ => {}
                        }
                    }
                    mem::drop(freeze_for_iteration);
                    Ok(Value::new_none())
                }
            }
            Stmt::Return(Some(e)) => {
                let e = self.expr(e);
                box move |context| {
                    before_stmt(span, context);
                    Err(EvalException::Return(e(context)?))
                }
            }
            Stmt::Return(None) => box move |context| {
                before_stmt(span, context);
                Err(EvalException::Return(Value::new_none()))
            },
            Stmt::If(cond, box then_block) => {
                let cond = self.expr(cond);
                let then_block = self.stmt(then_block);
                box move |context| {
                    before_stmt(span, context);
                    if cond(context)?.to_bool() {
                        then_block(context)
                    } else {
                        Ok(Value::new_none())
                    }
                }
            }
            Stmt::IfElse(cond, box (then_block, else_block)) => {
                let cond = self.expr(cond);
                let then_block = self.stmt(then_block);
                let else_block = self.stmt(else_block);
                box move |context| {
                    before_stmt(span, context);
                    if cond(context)?.to_bool() {
                        then_block(context)
                    } else {
                        else_block(context)
                    }
                }
            }
            Stmt::Statements(stmts) => {
                // No need to do before_stmt on these statements as they are
                // not meaningful statements
                let stmts = Stmt::flatten_statements(stmts);
                let mut stmts = stmts.into_map(|x| self.stmt(x));
                match stmts.len() {
                    0 => box move |_| Ok(Value::new_none()),
                    1 => stmts.pop().unwrap(),
                    _ => box move |context| {
                        let mut last = Value::new_none();
                        for stmt in &stmts {
                            last = stmt(context)?;
                        }
                        Ok(last)
                    },
                }
            }
            Stmt::Expression(e) => {
                let e = self.expr(e);
                box move |context| {
                    before_stmt(span, context);
                    e(context)
                }
            }
            Stmt::Assign(lhs, op, rhs) => {
                let rhs = self.expr(*rhs);
                match op {
                    AssignOp::Assign => {
                        let lhs = self.assign(*lhs);
                        box move |context| {
                            before_stmt(span, context);
                            lhs(rhs(context)?, context)?;
                            Ok(Value::new_none())
                        }
                    }
                    AssignOp::Add => self.assign_modify(span, *lhs, rhs, |l, r, context| {
                        add_assign(l, r, context.heap())
                    }),
                    AssignOp::Subtract => self
                        .assign_modify(span, *lhs, rhs, |l, r, context| l.sub(r, context.heap())),
                    AssignOp::Multiply => self
                        .assign_modify(span, *lhs, rhs, |l, r, context| l.mul(r, context.heap())),
                    AssignOp::FloorDivide => {
                        self.assign_modify(span, *lhs, rhs, |l, r, context| {
                            l.floor_div(r, context.heap())
                        })
                    }
                    AssignOp::Percent => self.assign_modify(span, *lhs, rhs, |l, r, context| {
                        l.percent(r, context.heap())
                    }),
                    AssignOp::BitAnd => self.assign_modify(span, *lhs, rhs, |l, r, _| l.bit_and(r)),
                    AssignOp::BitOr => self.assign_modify(span, *lhs, rhs, |l, r, _| l.bit_or(r)),
                    AssignOp::BitXor => self.assign_modify(span, *lhs, rhs, |l, r, _| l.bit_xor(r)),
                    AssignOp::LeftShift => {
                        self.assign_modify(span, *lhs, rhs, |l, r, _| l.left_shift(r))
                    }
                    AssignOp::RightShift => {
                        self.assign_modify(span, *lhs, rhs, |l, r, _| l.right_shift(r))
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
                box move |context| {
                    before_stmt(span, context);
                    let loadenv = match context.loader.as_mut() {
                        None => {
                            return Err(EvalException::Error(
                                EnvironmentError::NoImportsAvailable(name.to_owned()).into(),
                            ));
                        }
                        Some(load) => load.load(&name).map_err(EvalException::Error)?,
                    };
                    let modu = context.assert_module_env();
                    for (new_name, orig_name, span) in &symbols {
                        let value = thrw(modu.load_symbol(&loadenv, orig_name), *span, context)?;
                        match new_name {
                            Slot::Local(slot) => context.set_slot_local(*slot, value),
                            Slot::Module(slot) => context.set_slot_module(*slot, value),
                        }
                    }
                    Ok(Value::new_none())
                }
            }
            Stmt::Pass => box move |context| {
                before_stmt(span, context);
                Ok(Value::new_none())
            },
            Stmt::Break => box move |context| {
                before_stmt(span, context);
                Err(EvalException::Break)
            },
            Stmt::Continue => box move |context| {
                before_stmt(span, context);
                Err(EvalException::Continue)
            },
        }
    }
}
