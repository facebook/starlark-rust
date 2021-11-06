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
    eval::{
        compiler::{scope::CstExpr, Compiler},
        fragment::expr::ExprCompiledValue,
    },
    syntax::ast::ExprP,
    values::{dict::Dict, list::List},
};

/// Convert a list into a tuple. In many cases (iteration, `in`) these types
/// behave the same, but a list has identity and mutability, so much better to
/// switch to tuple where it makes no difference. A tuple of constants
/// will go on the FrozenHeap, while a list of constants will be continually
/// reallocated.
pub(crate) fn list_to_tuple(x: CstExpr) -> CstExpr {
    match x {
        Spanned {
            node: ExprP::List(x),
            span,
        } => Spanned {
            node: ExprP::Tuple(x),
            span,
        },
        _ => x,
    }
}

impl Compiler<'_, '_, '_> {
    /// Compile the operation `type(expr)`, trying to produce a constant
    /// where possible.
    pub fn fn_type(&mut self, expr: CstExpr) -> ExprCompiledValue {
        let span = expr.span;
        match self.expr(expr).node {
            ExprCompiledValue::Value(x) => {
                ExprCompiledValue::Value(x.to_value().get_type_value().unpack())
            }
            ExprCompiledValue::List(xs) if xs.is_empty() => {
                ExprCompiledValue::Value(List::get_type_value_static().unpack())
            }
            ExprCompiledValue::Dict(xs) if xs.is_empty() => {
                ExprCompiledValue::Value(Dict::get_type_value_static().unpack())
            }
            ExprCompiledValue::Tuple(xs) if xs.is_empty() => {
                unreachable!("empty tuple expression must have been compiled to value")
            }
            x => ExprCompiledValue::Type(box Spanned { node: x, span }),
        }
    }
}
