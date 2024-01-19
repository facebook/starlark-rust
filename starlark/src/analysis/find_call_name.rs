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

//! Linter.

use starlark_syntax::syntax::ast::Argument;
use starlark_syntax::syntax::ast::AstExpr;
use starlark_syntax::syntax::ast::AstLiteral;
use starlark_syntax::syntax::ast::Expr;
use starlark_syntax::syntax::module::AstModuleFields;

use crate::codemap::Span;
use crate::codemap::Spanned;
use crate::syntax::AstModule;

#[derive(Debug, PartialEq, Eq)]
/// Function calls that have a name attribute
pub struct NamedFunctionCall {
    /// The value of the name attribute passed to the function call
    pub name: String,
    /// The span of the function call
    pub span: Span,
}

/// Find the location of a top level function call that has a kwarg "name", and a string value
/// matching `name`.
pub trait AstModuleFindCallName {
    /// Find the location of a top level function call that has a kwarg "name", and a string value
    /// matching `name`.
    ///
    /// NOTE: If the AST is exposed in the future, this function may be removed and implemented
    ///       by specific programs instead.
    fn find_function_call_with_name(&self, name: &str) -> Option<Span>;

    /// Find all top level function calls that have a kwarg "name"
    fn find_named_function_calls(&self) -> Vec<NamedFunctionCall>;
}

impl AstModuleFindCallName for AstModule {
    fn find_function_call_with_name(&self, name: &str) -> Option<Span> {
        self.find_named_function_calls()
            .iter()
            .find(|call| call.name == name)
            .map(|call| call.span)
    }

    fn find_named_function_calls<'a>(&'a self) -> Vec<NamedFunctionCall> {
        let mut ret = Vec::new();

        fn visit_expr(ret: &mut Vec<NamedFunctionCall>, node: &AstExpr) {
            match node {
                Spanned {
                    node: Expr::Call(identifier, arguments),
                    ..
                } => {
                    if let Expr::Identifier(_) = &identifier.node {
                        let found = arguments.iter().find_map(|argument| match &argument.node {
                            Argument::Named(
                                arg_name,
                                Spanned {
                                    node: Expr::Literal(AstLiteral::String(s)),
                                    ..
                                },
                            ) if arg_name.node == "name" => Some(NamedFunctionCall {
                                name: s.node.clone(),
                                span: identifier.span,
                            }),
                            _ => None,
                        });
                        if let Some(found) = found {
                            ret.push(found);
                        }
                    }
                }
                _ => node.visit_expr(|x| visit_expr(ret, x)),
            }
        }

        self.statement().visit_expr(|x| visit_expr(&mut ret, x));
        ret
    }
}

#[cfg(test)]
mod test {
    use starlark_syntax::syntax::module::AstModuleFields;

    use crate::analysis::find_call_name::AstModuleFindCallName;
    use crate::codemap::ResolvedPos;
    use crate::codemap::ResolvedSpan;
    use crate::syntax::AstModule;
    use crate::syntax::Dialect;

    #[test]
    fn finds_function_calls_with_name_kwarg() -> anyhow::Result<()> {
        let contents = r#"
foo(name = "foo_name")
bar("bar_name")
baz(name = "baz_name")

def x(name = "foo_name"):
    pass
"#;

        let module = AstModule::parse("foo.star", contents.to_owned(), &Dialect::Extended).unwrap();

        assert_eq!(
            Some(ResolvedSpan {
                begin: ResolvedPos { line: 1, column: 0 },
                end: ResolvedPos { line: 1, column: 3 }
            }),
            module
                .find_function_call_with_name("foo_name")
                .map(|span| module.codemap().resolve_span(span))
        );
        assert_eq!(None, module.find_function_call_with_name("bar_name"));
        Ok(())
    }

    #[test]
    fn finds_all_named_function_calls() -> anyhow::Result<()> {
        let contents = r#"
foo(name = "foo_name")
bar("bar_name")
baz(name = "baz_name")

def x(name = "foo_name"):
    pass
"#;

        let module = AstModule::parse("foo.star", contents.to_owned(), &Dialect::Extended).unwrap();

        let calls = module.find_named_function_calls();

        assert_eq!(
            calls.iter().map(|call| &call.name).collect::<Vec<_>>(),
            &["foo_name", "baz_name"]
        );

        assert_eq!(
            calls
                .iter()
                .map(|call| module.codemap().resolve_span(call.span))
                .collect::<Vec<_>>(),
            &[
                ResolvedSpan {
                    begin: ResolvedPos { line: 1, column: 0 },
                    end: ResolvedPos { line: 1, column: 3 }
                },
                ResolvedSpan {
                    begin: ResolvedPos { line: 3, column: 0 },
                    end: ResolvedPos { line: 3, column: 3 }
                }
            ]
        );

        Ok(())
    }
}
