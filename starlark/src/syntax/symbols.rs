use std::collections::HashMap;

use crate::codemap::CodeMap;
use crate::codemap::LineCol;
use crate::docs::DocItem;
use crate::syntax::ast::AstPayload;
use crate::syntax::ast::AstStmtP;
use crate::syntax::ast::ExprP;
use crate::syntax::ast::ParameterP;
use crate::syntax::ast::StmtP;
use crate::syntax::docs::get_doc_item_for_def;

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
}

/// Walk the AST recursively and discover symbols.
pub(crate) fn find_symbols_at_location<P: AstPayload>(
    codemap: &CodeMap,
    ast: &AstStmtP<P>,
    cursor_position: LineCol,
) -> HashMap<String, Symbol> {
    let mut symbols = HashMap::new();
    fn walk<P: AstPayload>(
        codemap: &CodeMap,
        ast: &AstStmtP<P>,
        cursor_position: LineCol,
        symbols: &mut HashMap<String, Symbol>,
    ) {
        match &ast.node {
            StmtP::Assign(dest, rhs) => {
                let source = &rhs.as_ref().1;
                dest.visit_lvalue(|x| {
                    symbols.entry(x.0.to_string()).or_insert_with(|| Symbol {
                        name: x.0.to_string(),
                        kind: (match source.node {
                            ExprP::Lambda(_) => SymbolKind::Method,
                            _ => SymbolKind::Variable,
                        }),
                        detail: None,
                        doc: None,
                    });
                })
            }
            StmtP::AssignModify(dest, _, source) => dest.visit_lvalue(|x| {
                symbols.entry(x.0.to_string()).or_insert_with(|| Symbol {
                    name: x.0.to_string(),
                    kind: (match source.node {
                        ExprP::Lambda(_) => SymbolKind::Method,
                        _ => SymbolKind::Variable,
                    }),
                    detail: None,
                    doc: None,
                });
            }),
            StmtP::For(dest, over_body) => {
                let (_, body) = &**over_body;
                dest.visit_lvalue(|x| {
                    symbols.entry(x.0.to_string()).or_insert_with(|| Symbol {
                        name: x.0.to_string(),
                        kind: SymbolKind::Variable,
                        detail: None,
                        doc: None,
                    });
                });
                walk(codemap, body, cursor_position, symbols);
            }
            StmtP::Def(def) => {
                // Peek into the function definition to find the docstring.
                let doc = get_doc_item_for_def(def);
                symbols
                    .entry(def.name.0.to_string())
                    .or_insert_with(|| Symbol {
                        name: def.name.0.to_string(),
                        kind: SymbolKind::Method,
                        detail: None,
                        doc: doc.clone().map(DocItem::Function),
                    });

                // Only recurse into method if the cursor is in it.
                if codemap
                    .resolve_span(def.body.span)
                    .contains(cursor_position)
                {
                    symbols.extend(def.params.iter().filter_map(|param| match &param.node {
                        ParameterP::Normal(p, _) | ParameterP::WithDefaultValue(p, _, _) => Some((
                            p.0.to_string(),
                            Symbol {
                                name: p.0.clone(),
                                kind: SymbolKind::Variable,
                                detail: None,
                                doc: doc.as_ref().and_then(|doc| {
                                    doc.find_param_with_name(&p.0)
                                        .map(|param| DocItem::Param(param.clone()))
                                }),
                            },
                        )),
                        _ => None,
                    }));
                    walk(codemap, &def.body, cursor_position, symbols);
                }
            }
            StmtP::Load(load) => symbols.extend(load.args.iter().map(|(name, _)| {
                (
                    name.0.to_string(),
                    Symbol {
                        name: name.0.clone(),
                        detail: Some(format!("Loaded from {}", load.module.node)),
                        // TODO: This should be dynamic based on the actual loaded value.
                        kind: SymbolKind::Method,
                        // TODO: Pull from the original file.
                        doc: None,
                    },
                )
            })),
            stmt => stmt.visit_stmt(|x| walk(codemap, x, cursor_position, symbols)),
        }
    }

    walk(codemap, ast, cursor_position, &mut symbols);
    symbols
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::find_symbols_at_location;
    use super::Symbol;
    use super::SymbolKind;
    use crate::codemap::LineCol;
    use crate::syntax::AstModule;
    use crate::syntax::Dialect;

    #[test]
    fn global_symbols() {
        let ast_module = AstModule::parse(
            "t.star",
            r#"load("foo.star", "exported_a", renamed = "exported_b")

def method(param):
    pass

my_var = True
        "#
            .to_string(),
            &Dialect::Standard,
        )
        .unwrap();

        assert_eq!(
            find_symbols_at_location(
                &ast_module.codemap,
                &ast_module.statement,
                LineCol { line: 6, column: 0 },
            ),
            HashMap::from([
                (
                    "exported_a".to_string(),
                    Symbol {
                        name: "exported_a".to_string(),
                        detail: Some("Loaded from foo.star".to_string()),
                        kind: SymbolKind::Method,
                        doc: None,
                    },
                ),
                (
                    "renamed".to_string(),
                    Symbol {
                        name: "renamed".to_string(),
                        detail: Some("Loaded from foo.star".to_string()),
                        kind: SymbolKind::Method,
                        doc: None,
                    },
                ),
                (
                    "method".to_string(),
                    Symbol {
                        name: "method".to_string(),
                        detail: None,
                        kind: SymbolKind::Method,
                        doc: None,
                    },
                ),
                (
                    "my_var".to_string(),
                    Symbol {
                        name: "my_var".to_string(),
                        detail: None,
                        kind: SymbolKind::Variable,
                        doc: None,
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
            .to_string(),
            &Dialect::Standard,
        )
        .unwrap();

        assert_eq!(
            find_symbols_at_location(
                &ast_module.codemap,
                &ast_module.statement,
                LineCol { line: 3, column: 4 },
            ),
            HashMap::from([
                (
                    "exported_a".to_string(),
                    Symbol {
                        name: "exported_a".to_string(),
                        detail: Some("Loaded from foo.star".to_string()),
                        kind: SymbolKind::Method,
                        doc: None,
                    },
                ),
                (
                    "renamed".to_string(),
                    Symbol {
                        name: "renamed".to_string(),
                        detail: Some("Loaded from foo.star".to_string()),
                        kind: SymbolKind::Method,
                        doc: None,
                    },
                ),
                (
                    "method".to_string(),
                    Symbol {
                        name: "method".to_string(),
                        detail: None,
                        kind: SymbolKind::Method,
                        doc: None,
                    },
                ),
                (
                    "param".to_string(),
                    Symbol {
                        name: "param".to_string(),
                        detail: None,
                        kind: SymbolKind::Variable,
                        doc: None,
                    }
                ),
                (
                    "my_var".to_string(),
                    Symbol {
                        name: "my_var".to_string(),
                        detail: None,
                        kind: SymbolKind::Variable,
                        doc: None,
                    },
                ),
            ])
        );
    }
}
