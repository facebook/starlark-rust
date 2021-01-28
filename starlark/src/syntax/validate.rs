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

//! AST for parsed starlark files.

use crate::{
    errors::Diagnostic,
    syntax::{
        ast::{
            Argument, AstArgument, AstExpr, AstParameter, AstStmt, AstString, Expr, Parameter, Stmt,
        },
        lexer::LexerError,
    },
};
use codemap::{CodeMap, Spanned};
use gazebo::prelude::*;
use std::{collections::HashSet, sync::Arc};

#[derive(Eq, PartialEq, Ord, PartialOrd)]
enum ArgsStage {
    Positional,
    Named,
    Args,
    Kwargs,
}

impl Expr {
    pub fn check_call(f: Box<AstExpr>, args: Vec<AstArgument>) -> Result<Expr, LexerError> {
        let mut pos_args = Vec::new();
        let mut named_args = Vec::new();
        let mut args_array = None;
        let mut kwargs_dict = None;
        let mut stage = ArgsStage::Positional;
        for arg in args {
            match arg.node {
                Argument::Positional(s) => {
                    if stage != ArgsStage::Positional {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "positional argument after non positional",
                        });
                    } else {
                        pos_args.push(s);
                    }
                }
                Argument::Named(n, v) => {
                    if stage > ArgsStage::Named {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "named argument after *args or **kwargs",
                        });
                    } else {
                        stage = ArgsStage::Named;
                        named_args.push((n, v));
                    }
                }
                Argument::ArgsArray(v) => {
                    if stage > ArgsStage::Named {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "Args array after another args or kwargs",
                        });
                    } else {
                        stage = ArgsStage::Args;
                        args_array = Some(v);
                    }
                }
                Argument::KWArgsDict(d) => {
                    if stage == ArgsStage::Kwargs {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "Multiple kwargs dictionary in arguments",
                        });
                    } else {
                        stage = ArgsStage::Kwargs;
                        kwargs_dict = Some(d);
                    }
                }
            }
        }
        // Now check the names are distinct
        let mut named_set = HashSet::new();
        for (name, _) in &named_args {
            if !named_set.insert(&name.node) {
                return Err(LexerError::WrappedError {
                    span: name.span,
                    message: "repeated named argument",
                });
            }
        }
        Ok(Expr::Call(f, pos_args, named_args, args_array, kwargs_dict))
    }
}

fn test_param_name<'a, T>(
    argset: &mut HashSet<&'a str>,
    n: &'a Spanned<String>,
    arg: &Spanned<T>,
) -> Result<(), LexerError> {
    if argset.contains(n.node.as_str()) {
        return Err(LexerError::WrappedError {
            span: arg.span,
            message: "duplicated parameter name",
        });
    }
    argset.insert(&n.node);
    Ok(())
}

impl Stmt {
    pub fn check_def(
        name: AstString,
        parameters: Vec<AstParameter>,
        return_type: Option<Box<AstExpr>>,
        stmts: AstStmt,
    ) -> Result<Stmt, LexerError> {
        // you can't repeat argument names
        let mut argset = HashSet::new();
        // You can't have more than one *args/*, **kwargs
        // **kwargs must be last
        // You can't have a required `x` after an optional `y=1`
        let mut seen_args = false;
        let mut seen_kwargs = false;
        let mut seen_optional = false;

        for arg in parameters.iter() {
            match arg.node {
                Parameter::Normal(ref n, ..) => {
                    if seen_kwargs || seen_optional {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "positional parameter after non positional",
                        });
                    }
                    test_param_name(&mut argset, n, arg)?;
                }
                Parameter::WithDefaultValue(ref n, ..) => {
                    if seen_kwargs {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "Default parameter after args array or kwargs dictionary",
                        });
                    }
                    seen_optional = true;
                    test_param_name(&mut argset, n, arg)?;
                }
                Parameter::NoArgs => {
                    if seen_args || seen_kwargs {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "Args parameter after another args or kwargs parameter",
                        });
                    }
                    seen_args = true;
                }
                Parameter::Args(ref n, ..) => {
                    if seen_args || seen_kwargs {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "Args parameter after another args or kwargs parameter",
                        });
                    }
                    seen_args = true;
                    test_param_name(&mut argset, n, arg)?;
                }
                Parameter::KWArgs(ref n, ..) => {
                    if seen_kwargs {
                        return Err(LexerError::WrappedError {
                            span: arg.span,
                            message: "Multiple kwargs dictionary in parameters",
                        });
                    }
                    seen_kwargs = true;
                    test_param_name(&mut argset, n, arg)?;
                }
            }
        }
        Ok(Stmt::Def(name, parameters, return_type, box stmts))
    }

    /// Validate `break` and `continue` is only used inside loops
    pub fn validate_break_continue(codemap: &Arc<CodeMap>, stmt: &AstStmt) -> anyhow::Result<()> {
        // Inside a for, the only thing that might disallow break/continue is def
        fn inside_for(codemap: &Arc<CodeMap>, stmt: &AstStmt) -> anyhow::Result<()> {
            match stmt.node {
                Stmt::Def(_, _, _, ref body) => outside_for(codemap, body),
                _ => stmt.node.visit_stmt_result(|x| inside_for(codemap, x)),
            }
        }

        // Outside a for, a continue/break is an error
        fn outside_for(codemap: &Arc<CodeMap>, stmt: &AstStmt) -> anyhow::Result<()> {
            match stmt.node {
                Stmt::For(_, _, ref body) => inside_for(codemap, body),
                Stmt::Break | Stmt::Continue => {
                    let kw = if let Stmt::Break = stmt.node {
                        "break"
                    } else {
                        "continue"
                    };
                    let mut e = Diagnostic::new(format!("{} cannot be used outside of loop", kw));
                    e.set_span(stmt.span, codemap.dupe());
                    Err(e.into())
                }
                _ => stmt.node.visit_stmt_result(|x| outside_for(codemap, x)),
            }
        }

        outside_for(codemap, stmt)
    }
}
