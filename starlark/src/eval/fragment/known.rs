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

//! Things that operate on known values where we know we can do better.

use crate::{
    codemap::Spanned,
    eval::compiler::{Compiler, ExprCompiled, ExprCompiledValue},
    syntax::ast::{AstExpr, Expr},
    values::{dict::Dict, list::List},
};

/// Conditional statements are fairly common, some have literals (or imported values)
/// and quite a few start with a `not`, so encode those options statically.
pub(crate) enum Conditional {
    True,
    False,
    Normal(ExprCompiled),
    Negate(ExprCompiled),
}

impl Compiler<'_> {
    pub fn conditional(&mut self, expr: AstExpr) -> Conditional {
        let (expect, val) = match expr {
            Spanned {
                node: Expr::Not(box expr),
                ..
            } => (false, self.expr(expr)),
            _ => (true, self.expr(expr)),
        };
        match val {
            ExprCompiledValue::Value(x) => {
                if x.get_ref().to_bool() == expect {
                    Conditional::True
                } else {
                    Conditional::False
                }
            }
            ExprCompiledValue::Compiled(v) => {
                if expect {
                    Conditional::Normal(v)
                } else {
                    Conditional::Negate(v)
                }
            }
        }
    }

    /// Compile the operation `type(expr)`, trying to produce a constant
    /// where possible.
    pub fn fn_type(&mut self, expr: AstExpr) -> ExprCompiledValue {
        // Note that `type([fail("bad")])` must still raise an exception.
        // In practice people only really use the empty versions as constants.
        match &expr.node {
            Expr::Dict(xs) if xs.is_empty() => {
                return ExprCompiledValue::Value(self.heap.alloc_str(Dict::TYPE));
            }
            Expr::List(xs) if xs.is_empty() => {
                return ExprCompiledValue::Value(self.heap.alloc_str(List::TYPE));
            }
            // No need to handle Tuple as it will become frozen if it has no inner-calls
            _ => {}
        }
        match self.expr(expr) {
            ExprCompiledValue::Value(x) => ExprCompiledValue::Value(x.to_value().get_type_value()),
            ExprCompiledValue::Compiled(x) => {
                expr!("type", |eval| {
                    x(eval)?.get_ref().get_type_value().to_value()
                })
            }
        }
    }
}
