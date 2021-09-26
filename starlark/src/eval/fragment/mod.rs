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

// The paste pieces below are carefully structured so that the $name annotation
// makes it into the debug symbols, and is thus visible in system profilers (e.g. `perf`).

macro_rules! expr {
    ($name:expr, |$eval:ident| $body:expr) => {{
        paste::paste! {
            fn [<ann_expr_ $name>](
                f: impl for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Value<'v>, crate::eval::ExprEvalException>
                    + Send + Sync + 'static,
            ) -> ExprCompiled {
                #[allow(clippy::needless_question_mark)]
                box move |eval| f(eval)
            }
            let res: ExprCompiled = [<ann_expr_ $name>](move |$eval| {
                $eval.ann($name, |$eval| Ok($body))
            });
        }
        ExprCompiledValue::Compiled(res)
    }};
    ($name:expr, $v1:ident, |$eval:ident| $body:expr) => {{
        let $v1 = $v1.as_compiled();
        paste::paste! {
            fn [<ann_expr_ $name>](
                f: impl for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Value<'v>, crate::eval::ExprEvalException>
                    + Send + Sync + 'static,
            ) -> ExprCompiled {
                box move |eval| f(eval)
            }
            let res: ExprCompiled = [<ann_expr_ $name>](move |$eval| {
                let $v1 = $v1($eval)?;
                #[allow(clippy::needless_question_mark)]
                $eval.ann($name, |$eval| Ok($body))
            });
        }
        ExprCompiledValue::Compiled(res)
    }};
    ($name:expr, $v1:ident, $v2:ident, |$eval:ident| $body:expr) => {{
        let $v1 = $v1.as_compiled();
        let $v2 = $v2.as_compiled();
        paste::paste! {
            fn [<ann_expr_ $name>](
                f: impl for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<Value<'v>, crate::eval::ExprEvalException>
                    + Send + Sync + 'static,
            ) -> ExprCompiled {
                box move |eval| f(eval)
            }
            let res: ExprCompiled = [<ann_expr_ $name>](move |$eval| {
                let $v1 = $v1($eval)?;
                let $v2 = $v2($eval)?;
                #[allow(clippy::needless_question_mark)]
                $eval.ann($name, |$eval| Ok($body))
            });
        }
        ExprCompiledValue::Compiled(res)
    }};
}

macro_rules! value {
    ($v:expr) => {
        ExprCompiledValue::Value($v)
    };
}

macro_rules! stmt {
    ($self:ident, $name:expr, $span:ident, |$eval:ident| $body:expr) => {{
        paste::paste! {
            fn [<ann_stmt_ $name>](
                f: impl for<'v> Fn(&mut Evaluator<'v, '_>) -> Result<(), EvalException<'v>>
                    + Send + Sync + 'static,
            ) -> StmtsCompiled {
                StmtsCompiled::one(StmtCompiledValue::Compiled(box move |eval| f(eval)))
            }
            $self.maybe_wrap_before_stmt($span, [<ann_stmt_ $name>](move |$eval|
                $eval.ann($name, |$eval| {
                    $body;
                    #[allow(unreachable_code)]
                    Ok(())
                })
            ))
        }
    }};
}

pub(crate) mod call;
pub(crate) mod compr;
pub(crate) mod def;
pub(crate) mod expr;
pub(crate) mod known;
pub(crate) mod module;
pub(crate) mod stmt;
