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

//! Compile function calls.

use crate::{
    codemap::Span,
    collections::symbol_map::Symbol,
    eval::{
        compiler::{
            scope::{CstArgument, CstExpr},
            throw, Compiler, EvalException, ExprCompiled, ExprCompiledValue,
        },
        fragment::expr::get_attr_hashed,
        Arguments, Evaluator,
    },
    syntax::ast::{ArgumentP, ExprP},
    values::{FrozenValue, Value, ValueLike},
};
use gazebo::coerce::coerce_ref;
use std::mem::MaybeUninit;

#[derive(Default)]
struct ArgsCompiled {
    pos_named: Vec<ExprCompiled>,
    /// Named arguments compiled.
    ///
    /// Note names are guaranteed to be unique here because names are validated in AST:
    /// named arguments in [`Expr::Call`] are unique.
    names: Vec<(Symbol, FrozenValue)>,
    args: Option<ExprCompiled>,
    kwargs: Option<ExprCompiled>,
}

/// Specialized version of [`ArgsCompiled`] for faster evaluation.
///
/// This is meant to be used with [`args!`] macro.
enum ArgsCompiledSpec {
    Args0(Args0Compiled),
    Args1(Args1Compiled),
    Args2(Args2Compiled),
    Args(ArgsCompiled),
}

impl ArgsCompiled {
    fn spec(mut self) -> ArgsCompiledSpec {
        if self.names.is_empty()
            && self.args.is_none()
            && self.kwargs.is_none()
            && self.pos_named.len() <= 2
        {
            match self.pos_named.pop() {
                None => ArgsCompiledSpec::Args0(Args0Compiled),
                Some(a1) => match self.pos_named.pop() {
                    None => ArgsCompiledSpec::Args1(Args1Compiled(a1)),
                    Some(a2) => ArgsCompiledSpec::Args2(Args2Compiled(a2, a1)),
                },
            }
        } else {
            ArgsCompiledSpec::Args(self)
        }
    }
}

// Helper that creates some specialised argument calls
macro_rules! args {
    ($args:ident, $e:expr) => {
        match $args.spec() {
            ArgsCompiledSpec::Args0($args) => $e,
            ArgsCompiledSpec::Args1($args) => $e,
            ArgsCompiledSpec::Args2($args) => $e,
            ArgsCompiledSpec::Args($args) => $e,
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
        f: impl FnOnce(Arguments<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        let params = Arguments {
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
        f: impl FnOnce(Arguments<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        let params = Arguments {
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
        f: impl FnOnce(Arguments<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
    ) -> Result<R, EvalException<'v>> {
        let params = Arguments {
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
        f: impl FnOnce(Arguments<'v, '_>, &mut Evaluator<'v, '_>) -> Result<R, EvalException<'v>>,
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
            let params = Arguments {
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

impl Compiler<'_> {
    fn args(&mut self, args: Vec<CstArgument>) -> ArgsCompiled {
        let mut res = ArgsCompiled::default();
        for x in args {
            match x.node {
                ArgumentP::Positional(x) => res.pos_named.push(self.expr(x).as_compiled()),
                ArgumentP::Named(name, value) => {
                    let fv = self.module_env.frozen_heap().alloc(name.node.as_str());
                    res.names.push((Symbol::new(&name.node), fv));
                    res.pos_named.push(self.expr(value).as_compiled());
                }
                ArgumentP::Args(x) => res.args = Some(self.expr(x).as_compiled()),
                ArgumentP::KwArgs(x) => res.kwargs = Some(self.expr(x).as_compiled()),
            }
        }
        res
    }

    pub(crate) fn expr_call(
        &mut self,
        span: Span,
        left: CstExpr,
        mut args: Vec<CstArgument>,
    ) -> ExprCompiledValue {
        match left.node {
            ExprP::Dot(box e, s) => {
                let e = self.expr(e);
                let s = Symbol::new(&s.node);
                let args = self.args(args);
                if let Some(e) = e.as_value() {
                    if let Some((_, fun)) = self.compile_time_getattr(e, &s) {
                        return args!(
                            args,
                            expr!("call_method_getattr_cached", |eval| {
                                // This code is identical to non-const-propagated branch
                                // below. But these branches are hard to merge
                                // because of `args! macro`.
                                args.with_params(Some(e.to_value()), eval, |params, eval| {
                                    throw(fun.invoke(Some(span), params, eval), span, eval)
                                })?
                            })
                        );
                    }
                }
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
                let left = self.expr(left);
                let one_positional = args.len() == 1 && args[0].is_positional();
                if left.as_value() == Some(self.constants.fn_type) && one_positional {
                    self.fn_type(args.pop().unwrap().node.into_expr())
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
}
