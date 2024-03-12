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

//! Find which symbols are in scope at a particular point.

use std::collections::HashMap;
use std::ops::Deref;

use lsp_types::DocumentSymbol;
use lsp_types::SymbolKind as LspSymbolKind;
use starlark::codemap::CodeMap;
use starlark::codemap::Span;
use starlark::docs::DocItem;
use starlark::docs::DocParam;
use starlark_syntax::codemap::ResolvedPos;
use starlark_syntax::syntax::ast::ArgumentP;
use starlark_syntax::syntax::ast::AssignP;
use starlark_syntax::syntax::ast::AssignTargetP;
use starlark_syntax::syntax::ast::AstAssignIdentP;
use starlark_syntax::syntax::ast::AstExprP;
use starlark_syntax::syntax::ast::AstLiteral;
use starlark_syntax::syntax::ast::AstPayload;
use starlark_syntax::syntax::ast::AstStmtP;
use starlark_syntax::syntax::ast::ExprP;
use starlark_syntax::syntax::ast::ForP;
use starlark_syntax::syntax::ast::LoadArgP;
use starlark_syntax::syntax::ast::ParameterP;
use starlark_syntax::syntax::ast::StmtP;

use crate::docs::get_doc_item_for_def;

#[derive(Debug, PartialEq)]
pub(crate) enum SymbolKind {
    Method,
    Variable,
}

#[derive(Debug, PartialEq)]
pub(crate) struct Symbol {
    pub(crate) name: String,
    pub(crate) detail: Option<String>,
    pub(crate) kind: SymbolKind,
    pub(crate) doc: Option<DocItem>,
    pub(crate) param: Option<DocParam>,
}

/// Walk the AST recursively and discover symbols.
pub(crate) fn find_symbols_at_location<P: AstPayload>(
    codemap: &CodeMap,
    ast: &AstStmtP<P>,
    cursor_position: ResolvedPos,
) -> HashMap<String, Symbol> {
    let mut symbols = HashMap::new();
    fn walk<P: AstPayload>(
        codemap: &CodeMap,
        ast: &AstStmtP<P>,
        cursor_position: ResolvedPos,
        symbols: &mut HashMap<String, Symbol>,
    ) {
        match &ast.node {
            StmtP::Assign(AssignP { lhs, ty: _, rhs }) => lhs.visit_lvalue(|x| {
                symbols.entry(x.ident.clone()).or_insert_with(|| Symbol {
                    name: x.ident.clone(),
                    kind: (match rhs.node {
                        ExprP::Lambda(_) => SymbolKind::Method,
                        _ => SymbolKind::Variable,
                    }),
                    detail: None,
                    doc: None,
                    param: None,
                });
            }),
            StmtP::AssignModify(dest, _, source) => dest.visit_lvalue(|x| {
                symbols.entry(x.ident.clone()).or_insert_with(|| Symbol {
                    name: x.ident.clone(),
                    kind: (match source.node {
                        ExprP::Lambda(_) => SymbolKind::Method,
                        _ => SymbolKind::Variable,
                    }),
                    detail: None,
                    doc: None,
                    param: None,
                });
            }),
            StmtP::For(ForP { var, over: _, body }) => {
                var.visit_lvalue(|x| {
                    symbols.entry(x.ident.clone()).or_insert_with(|| Symbol {
                        name: x.ident.clone(),
                        kind: SymbolKind::Variable,
                        detail: None,
                        doc: None,
                        param: None,
                    });
                });
                walk(codemap, body, cursor_position, symbols);
            }
            StmtP::Def(def) => {
                // Peek into the function definition to find the docstring.
                let doc = get_doc_item_for_def(def);
                symbols
                    .entry(def.name.ident.clone())
                    .or_insert_with(|| Symbol {
                        name: def.name.ident.clone(),
                        kind: SymbolKind::Method,
                        detail: None,
                        doc: doc.clone().map(DocItem::Function),
                        param: None,
                    });

                // Only recurse into method if the cursor is in it.
                if codemap
                    .resolve_span(def.body.span)
                    .contains(cursor_position)
                {
                    symbols.extend(def.params.iter().filter_map(|param| match &param.node {
                        ParameterP::Normal(p, _) | ParameterP::WithDefaultValue(p, _, _) => {
                            Some((
                                p.ident.clone(),
                                Symbol {
                                    name: p.ident.clone(),
                                    kind: SymbolKind::Variable,
                                    detail: None,
                                    doc: None,
                                    param: doc.as_ref().and_then(|doc| {
                                        doc.find_param_with_name(&p.ident).cloned()
                                    }),
                                },
                            ))
                        }
                        _ => None,
                    }));
                    walk(codemap, &def.body, cursor_position, symbols);
                }
            }
            StmtP::Load(load) => {
                symbols.extend(load.args.iter().map(|LoadArgP { local, .. }| {
                    (
                        local.ident.clone(),
                        Symbol {
                            name: local.ident.clone(),
                            detail: Some(format!("Loaded from {}", load.module.node)),
                            // TODO: This should be dynamic based on the actual loaded value.
                            kind: SymbolKind::Method,
                            // TODO: Pull from the original file.
                            doc: None,
                            param: None,
                        },
                    )
                }))
            }
            stmt => stmt.visit_stmt(|x| walk(codemap, x, cursor_position, symbols)),
        }
    }

    walk(codemap, ast, cursor_position, &mut symbols);
    symbols
}

pub fn get_document_symbols<P: AstPayload>(
    codemap: &CodeMap,
    ast: &AstStmtP<P>,
) -> Vec<DocumentSymbol> {
    let mut symbols = Vec::new();
    match &ast.node {
        StmtP::Expression(expr) => {
            if let Some(symbol) = get_document_symbol_for_expr(codemap, None, expr, ast.span) {
                symbols.push(symbol);
            }
        }
        StmtP::Assign(assign) => {
            if let Some(symbol) = get_document_symbol_for_expr(
                codemap,
                match &assign.lhs.node {
                    AssignTargetP::Tuple(_)
                    | AssignTargetP::Index(_)
                    | AssignTargetP::Dot(_, _) => None,
                    AssignTargetP::Identifier(ident) => Some(ident),
                },
                &assign.rhs,
                ast.span,
            ) {
                symbols.push(symbol);
            }
        }
        StmtP::Statements(statements) => {
            for stmt in statements {
                symbols.extend(get_document_symbols(codemap, stmt));
            }
        }
        StmtP::If(_, body) => {
            symbols.extend(get_document_symbols(codemap, body));
        }
        StmtP::IfElse(_, bodies) => {
            let (if_body, else_body) = bodies.deref();
            symbols.extend(get_document_symbols(codemap, if_body));
            symbols.extend(get_document_symbols(codemap, else_body));
        }
        StmtP::For(for_) => {
            symbols.extend(get_document_symbols(codemap, &for_.body));
        }
        StmtP::Def(def) => {
            symbols.push(make_document_symbol(
                def.name.ident.clone(),
                LspSymbolKind::FUNCTION,
                ast.span,
                def.name.span,
                codemap,
                Some(
                    def.params
                        .iter()
                        .filter_map(|param| get_document_symbol_for_parameter(codemap, param))
                        .chain(get_document_symbols(codemap, &def.body))
                        .collect(),
                ),
            ));
        }
        StmtP::Load(load) => {
            symbols.push(make_document_symbol(
                load.module.node.clone(),
                LspSymbolKind::MODULE,
                ast.span,
                load.module.span,
                codemap,
                Some(
                    load.args
                        .iter()
                        .map(|loaded_symbol| {
                            make_document_symbol(
                                loaded_symbol.local.ident.clone(),
                                LspSymbolKind::METHOD,
                                loaded_symbol.span(),
                                loaded_symbol.local.span,
                                codemap,
                                None,
                            )
                        })
                        .collect(),
                ),
            ));
        }

        // These don't produce any symbols.
        StmtP::Break
        | StmtP::Continue
        | StmtP::Pass
        | StmtP::Return(_)
        | StmtP::AssignModify(_, _, _) => {}
    }

    symbols
}

fn get_document_symbol_for_parameter<P: AstPayload>(
    codemap: &CodeMap,
    param: &ParameterP<P>,
) -> Option<DocumentSymbol> {
    match param {
        ParameterP::NoArgs => None,
        ParameterP::Normal(p, _)
        | ParameterP::WithDefaultValue(p, _, _)
        | ParameterP::Args(p, _)
        | ParameterP::KwArgs(p, _) => Some(make_document_symbol(
            p.ident.clone(),
            LspSymbolKind::VARIABLE,
            p.span,
            p.span,
            codemap,
            None,
        )),
    }
}

fn get_document_symbol_for_expr<P: AstPayload>(
    codemap: &CodeMap,
    name: Option<&AstAssignIdentP<P>>,
    expr: &AstExprP<P>,
    outer_range: Span,
) -> Option<DocumentSymbol> {
    match &expr.node {
        ExprP::Call(call, args) => {
            if let ExprP::Identifier(func_name) = &call.node {
                // Look for a call to `struct`. We'll require passing in a name from the assignment
                // expression. The outer range is the range of the entire assignment expression.
                if &func_name.node.ident == "struct" {
                    name.map(|name| {
                        make_document_symbol(
                            name.ident.clone(),
                            LspSymbolKind::STRUCT,
                            outer_range,
                            name.span,
                            codemap,
                            Some(
                                args.iter()
                                    .filter_map(|arg| match &arg.node {
                                        ArgumentP::Named(name, _) => Some(make_document_symbol(
                                            name.node.clone(),
                                            LspSymbolKind::FIELD,
                                            arg.span,
                                            name.span,
                                            codemap,
                                            None,
                                        )),
                                        _ => None,
                                    })
                                    .collect(),
                            ),
                        )
                    })
                } else {
                    // Check if this call has a named argument called "name". If so, we'll assume
                    // that this is a buildable target, and expose it.
                    args.iter()
                        .find_map(|arg| match &arg.node {
                            ArgumentP::Named(name, value) => match (name, &value.node) {
                                (name, ExprP::Literal(AstLiteral::String(value)))
                                    if &name.node == "name" =>
                                {
                                    Some(value)
                                }
                                _ => None,
                            },
                            _ => None,
                        })
                        .map(|target_name| {
                            make_document_symbol(
                                target_name.node.clone(),
                                LspSymbolKind::CONSTANT,
                                expr.span,
                                target_name.span,
                                codemap,
                                None,
                            )
                        })
                }
            } else {
                None
            }
        }
        ExprP::Lambda(lambda) => name.map(|name| {
            make_document_symbol(
                name.ident.clone(),
                LspSymbolKind::FUNCTION,
                expr.span,
                expr.span,
                codemap,
                Some(
                    lambda
                        .params
                        .iter()
                        .filter_map(|param| get_document_symbol_for_parameter(codemap, param))
                        .chain(get_document_symbol_for_expr(
                            codemap,
                            None,
                            &lambda.body,
                            lambda.body.span,
                        ))
                        .collect(),
                ),
            )
        }),

        _ => None,
    }
}

fn make_document_symbol(
    name: String,
    kind: LspSymbolKind,
    range: Span,
    selection_range: Span,
    codemap: &CodeMap,
    children: Option<Vec<DocumentSymbol>>,
) -> DocumentSymbol {
    #[allow(deprecated)]
    DocumentSymbol {
        name,
        detail: None,
        kind,
        tags: None,
        deprecated: None,
        range: codemap.resolve_span(range).into(),
        selection_range: codemap.resolve_span(selection_range).into(),
        children,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use lsp_types::DocumentSymbol;
    use lsp_types::Position;
    use lsp_types::Range;
    use lsp_types::SymbolKind as LspSymbolKind;
    use starlark::syntax::AstModule;
    use starlark::syntax::Dialect;
    use starlark_syntax::codemap::ResolvedPos;
    use starlark_syntax::syntax::module::AstModuleFields;

    use super::find_symbols_at_location;
    use super::get_document_symbols;
    use super::Symbol;
    use super::SymbolKind;

    #[test]
    fn global_symbols() {
        let ast_module = AstModule::parse(
            "t.star",
            r#"load("foo.star", "exported_a", renamed = "exported_b")

def method(param):
    pass

my_var = True
        "#
            .to_owned(),
            &Dialect::Standard,
        )
        .unwrap();

        assert_eq!(
            find_symbols_at_location(
                ast_module.codemap(),
                ast_module.statement(),
                ResolvedPos { line: 6, column: 0 },
            ),
            HashMap::from([
                (
                    "exported_a".to_owned(),
                    Symbol {
                        name: "exported_a".to_owned(),
                        detail: Some("Loaded from foo.star".to_owned()),
                        kind: SymbolKind::Method,
                        doc: None,
                        param: None,
                    },
                ),
                (
                    "renamed".to_owned(),
                    Symbol {
                        name: "renamed".to_owned(),
                        detail: Some("Loaded from foo.star".to_owned()),
                        kind: SymbolKind::Method,
                        doc: None,
                        param: None,
                    },
                ),
                (
                    "method".to_owned(),
                    Symbol {
                        name: "method".to_owned(),
                        detail: None,
                        kind: SymbolKind::Method,
                        doc: None,
                        param: None,
                    },
                ),
                (
                    "my_var".to_owned(),
                    Symbol {
                        name: "my_var".to_owned(),
                        detail: None,
                        kind: SymbolKind::Variable,
                        doc: None,
                        param: None,
                    },
                ),
            ])
        );
    }

    #[test]
    fn inside_method() {
        let ast_module = AstModule::parse(
            "t.star",
            r#"load("foo.star", "exported_a", renamed = "exported_b")

def method(param):
    pass

my_var = True
        "#
            .to_owned(),
            &Dialect::Standard,
        )
        .unwrap();

        assert_eq!(
            find_symbols_at_location(
                ast_module.codemap(),
                ast_module.statement(),
                ResolvedPos { line: 3, column: 4 },
            ),
            HashMap::from([
                (
                    "exported_a".to_owned(),
                    Symbol {
                        name: "exported_a".to_owned(),
                        detail: Some("Loaded from foo.star".to_owned()),
                        kind: SymbolKind::Method,
                        doc: None,
                        param: None,
                    },
                ),
                (
                    "renamed".to_owned(),
                    Symbol {
                        name: "renamed".to_owned(),
                        detail: Some("Loaded from foo.star".to_owned()),
                        kind: SymbolKind::Method,
                        doc: None,
                        param: None,
                    },
                ),
                (
                    "method".to_owned(),
                    Symbol {
                        name: "method".to_owned(),
                        detail: None,
                        kind: SymbolKind::Method,
                        doc: None,
                        param: None,
                    },
                ),
                (
                    "param".to_owned(),
                    Symbol {
                        name: "param".to_owned(),
                        detail: None,
                        kind: SymbolKind::Variable,
                        doc: None,
                        param: None,
                    }
                ),
                (
                    "my_var".to_owned(),
                    Symbol {
                        name: "my_var".to_owned(),
                        detail: None,
                        kind: SymbolKind::Variable,
                        doc: None,
                        param: None,
                    },
                ),
            ])
        );
    }

    #[test]
    fn document_symbols() {
        let ast_module = AstModule::parse(
            "t.star",
            r#"load("foo.star", "exported_a", renamed = "exported_b")

def method(param):
    foo = struct(field = "value")
    bar = lambda x: x + 1
    return lambda y: y + 1

baz = struct(field = "value")

some_rule(name = "qux")
        "#
            .to_owned(),
            &Dialect::Standard,
        )
        .unwrap();

        assert_eq!(
            get_document_symbols(ast_module.codemap(), ast_module.statement()),
            vec![
                #[allow(deprecated)]
                DocumentSymbol {
                    name: "foo.star".to_owned(),
                    detail: None,
                    kind: LspSymbolKind::MODULE,
                    tags: None,
                    deprecated: None,
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0
                        },
                        end: Position {
                            line: 0,
                            character: 54
                        }
                    },
                    selection_range: Range {
                        start: Position {
                            line: 0,
                            character: 5
                        },
                        end: Position {
                            line: 0,
                            character: 15
                        }
                    },
                    children: Some(vec![
                        DocumentSymbol {
                            name: "exported_a".to_owned(),
                            detail: None,
                            kind: LspSymbolKind::METHOD,
                            tags: None,
                            deprecated: None,
                            range: Range {
                                start: Position {
                                    line: 0,
                                    character: 17
                                },
                                end: Position {
                                    line: 0,
                                    character: 29
                                }
                            },
                            selection_range: Range {
                                start: Position {
                                    line: 0,
                                    character: 17
                                },
                                end: Position {
                                    line: 0,
                                    character: 29
                                }
                            },
                            children: None
                        },
                        DocumentSymbol {
                            name: "renamed".to_owned(),
                            detail: None,
                            kind: LspSymbolKind::METHOD,
                            tags: None,
                            deprecated: None,
                            range: Range {
                                start: Position {
                                    line: 0,
                                    character: 31
                                },
                                end: Position {
                                    line: 0,
                                    character: 53
                                }
                            },
                            selection_range: Range {
                                start: Position {
                                    line: 0,
                                    character: 31
                                },
                                end: Position {
                                    line: 0,
                                    character: 38
                                }
                            },
                            children: None
                        }
                    ])
                },
                #[allow(deprecated)]
                DocumentSymbol {
                    name: "method".to_owned(),
                    detail: None,
                    kind: LspSymbolKind::FUNCTION,
                    tags: None,
                    deprecated: None,
                    range: Range {
                        start: Position {
                            line: 2,
                            character: 0
                        },
                        end: Position {
                            line: 7,
                            character: 0
                        }
                    },
                    selection_range: Range {
                        start: Position {
                            line: 2,
                            character: 4
                        },
                        end: Position {
                            line: 2,
                            character: 10
                        }
                    },
                    children: Some(vec![
                        DocumentSymbol {
                            name: "param".to_owned(),
                            detail: None,
                            kind: LspSymbolKind::VARIABLE,
                            tags: None,
                            deprecated: None,
                            range: Range {
                                start: Position {
                                    line: 2,
                                    character: 11
                                },
                                end: Position {
                                    line: 2,
                                    character: 16
                                }
                            },
                            selection_range: Range {
                                start: Position {
                                    line: 2,
                                    character: 11
                                },
                                end: Position {
                                    line: 2,
                                    character: 16
                                }
                            },
                            children: None
                        },
                        DocumentSymbol {
                            name: "foo".to_owned(),
                            detail: None,
                            kind: LspSymbolKind::STRUCT,
                            tags: None,
                            deprecated: None,
                            range: Range {
                                start: Position {
                                    line: 3,
                                    character: 4
                                },
                                end: Position {
                                    line: 3,
                                    character: 33
                                }
                            },
                            selection_range: Range {
                                start: Position {
                                    line: 3,
                                    character: 4
                                },
                                end: Position {
                                    line: 3,
                                    character: 7
                                }
                            },
                            children: Some(vec![DocumentSymbol {
                                name: "field".to_owned(),
                                detail: None,
                                kind: LspSymbolKind::FIELD,
                                tags: None,
                                deprecated: None,
                                range: Range {
                                    start: Position {
                                        line: 3,
                                        character: 17
                                    },
                                    end: Position {
                                        line: 3,
                                        character: 32
                                    }
                                },
                                selection_range: Range {
                                    start: Position {
                                        line: 3,
                                        character: 17
                                    },
                                    end: Position {
                                        line: 3,
                                        character: 22
                                    }
                                },
                                children: None
                            }])
                        },
                        DocumentSymbol {
                            name: "bar".to_owned(),
                            detail: None,
                            kind: LspSymbolKind::FUNCTION,
                            tags: None,
                            deprecated: None,
                            range: Range {
                                start: Position {
                                    line: 4,
                                    character: 10
                                },
                                end: Position {
                                    line: 4,
                                    character: 25
                                }
                            },
                            selection_range: Range {
                                start: Position {
                                    line: 4,
                                    character: 10
                                },
                                end: Position {
                                    line: 4,
                                    character: 25
                                }
                            },
                            children: Some(vec![DocumentSymbol {
                                name: "x".to_owned(),
                                detail: None,
                                kind: LspSymbolKind::VARIABLE,
                                tags: None,
                                deprecated: None,
                                range: Range {
                                    start: Position {
                                        line: 4,
                                        character: 17
                                    },
                                    end: Position {
                                        line: 4,
                                        character: 18
                                    }
                                },
                                selection_range: Range {
                                    start: Position {
                                        line: 4,
                                        character: 17
                                    },
                                    end: Position {
                                        line: 4,
                                        character: 18
                                    }
                                },
                                children: None
                            }])
                        }
                    ])
                },
                #[allow(deprecated)]
                DocumentSymbol {
                    name: "baz".to_owned(),
                    detail: None,
                    kind: LspSymbolKind::STRUCT,
                    tags: None,
                    deprecated: None,
                    range: Range {
                        start: Position {
                            line: 7,
                            character: 0
                        },
                        end: Position {
                            line: 7,
                            character: 29
                        }
                    },
                    selection_range: Range {
                        start: Position {
                            line: 7,
                            character: 0
                        },
                        end: Position {
                            line: 7,
                            character: 3
                        }
                    },
                    children: Some(vec![DocumentSymbol {
                        name: "field".to_owned(),
                        detail: None,
                        kind: LspSymbolKind::FIELD,
                        tags: None,
                        deprecated: None,
                        range: Range {
                            start: Position {
                                line: 7,
                                character: 13
                            },
                            end: Position {
                                line: 7,
                                character: 28
                            }
                        },
                        selection_range: Range {
                            start: Position {
                                line: 7,
                                character: 13
                            },
                            end: Position {
                                line: 7,
                                character: 18
                            }
                        },
                        children: None
                    }])
                },
                #[allow(deprecated)]
                DocumentSymbol {
                    name: "qux".to_owned(),
                    detail: None,
                    kind: LspSymbolKind::CONSTANT,
                    tags: None,
                    deprecated: None,
                    range: Range {
                        start: Position {
                            line: 9,
                            character: 0
                        },
                        end: Position {
                            line: 9,
                            character: 23
                        }
                    },
                    selection_range: Range {
                        start: Position {
                            line: 9,
                            character: 17
                        },
                        end: Position {
                            line: 9,
                            character: 22
                        }
                    },
                    children: None
                }
            ]
        )
    }
}
