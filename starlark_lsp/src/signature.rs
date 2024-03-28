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

use starlark::codemap::CodeMap;
use starlark::codemap::ResolvedPos;
use starlark::codemap::ResolvedSpan;
use starlark_syntax::syntax::ast::ArgumentP;
use starlark_syntax::syntax::ast::AstExprP;
use starlark_syntax::syntax::ast::AstPayload;
use starlark_syntax::syntax::ast::ExprP;
use starlark_syntax::syntax::module::AstModuleFields;

use crate::definition::LspModule;

#[derive(Debug)]
pub(crate) struct Call {
    pub(crate) function_span: ResolvedSpan,
    pub(crate) current_argument: CallArgument,
}

#[derive(Debug)]
pub(crate) enum CallArgument {
    Positional(usize),
    Named(String),
    None,
}

pub(crate) fn function_signatures(
    ast: &LspModule,
    line: u32,
    character: u32,
) -> anyhow::Result<Vec<Call>> {
    let pos = ResolvedPos {
        line: line as usize,
        column: character as usize,
    };

    let mut calls = Vec::new();
    ast.ast
        .statement()
        .visit_expr(|expr| visit_expr(expr, &mut calls, ast.ast.codemap(), pos));

    Ok(calls)
}

fn visit_expr<P: AstPayload>(
    expr: &AstExprP<P>,
    calls: &mut Vec<Call>,
    codemap: &CodeMap,
    pos: ResolvedPos,
) {
    let expr_span = codemap.resolve_span(expr.span);
    if !expr_span.contains(pos) {
        return;
    }

    if let ExprP::Call(target, args) = &expr.node {
        if let ExprP::Identifier(ident) = &target.node {
            let current_argument = args
                .iter()
                .enumerate()
                .find_map(|(i, arg)| {
                    let arg_span = codemap.resolve_span(arg.span);
                    if !arg_span.contains(pos) {
                        return None;
                    }

                    match &arg.node {
                        ArgumentP::Positional(_) => Some(CallArgument::Positional(i)),
                        ArgumentP::Named(name, _) => Some(CallArgument::Named(name.node.clone())),
                        ArgumentP::Args(_) => todo!(),
                        ArgumentP::KwArgs(_) => todo!(),
                    }
                })
                .unwrap_or({
                    if args.is_empty() {
                        CallArgument::None
                    } else {
                        CallArgument::Positional(args.len())
                    }
                });

            calls.push(Call {
                function_span: codemap.resolve_span(ident.span),
                current_argument,
            });
        }
    }

    expr.visit_expr(|expr| visit_expr(expr, calls, codemap, pos));
}
