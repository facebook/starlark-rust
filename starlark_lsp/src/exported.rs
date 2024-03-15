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

use lsp_types::CompletionItem;
use lsp_types::Documentation;
use lsp_types::MarkupContent;
use lsp_types::MarkupKind;
use starlark::collections::SmallMap;
use starlark::docs::markdown::render_doc_item;
use starlark::docs::DocMember;
use starlark::syntax::AstModule;
use starlark_syntax::syntax::ast::AstAssignIdent;
use starlark_syntax::syntax::ast::Stmt;
use starlark_syntax::syntax::module::AstModuleFields;
use starlark_syntax::syntax::top_level_stmts::top_level_stmts;

use crate::docs::get_doc_item_for_assign;
use crate::docs::get_doc_item_for_def;
use crate::symbols::MethodSymbolArgument;
use crate::symbols::Symbol;
use crate::symbols::SymbolKind;

impl From<Symbol> for CompletionItem {
    fn from(value: Symbol) -> Self {
        let documentation = value.doc.map(|doc| {
            Documentation::MarkupContent(MarkupContent {
                kind: MarkupKind::Markdown,
                value: render_doc_item(&value.name, &doc.to_doc_item()),
            })
        });
        Self {
            label: value.name,
            kind: Some(value.kind.into()),
            documentation,
            ..Default::default()
        }
    }
}

pub(crate) trait AstModuleExportedSymbols {
    /// Which symbols are exported by this module. These are the top-level assignments,
    /// including function definitions. Any symbols that start with `_` are not exported.
    fn exported_symbols(&self) -> Vec<Symbol>;
}

impl AstModuleExportedSymbols for AstModule {
    fn exported_symbols(&self) -> Vec<Symbol> {
        // Map since we only want to store the first of each export
        // IndexMap since we want the order to match the order they were defined in
        let mut result: SmallMap<&str, _> = SmallMap::new();

        fn add<'a>(
            result: &mut SmallMap<&'a str, Symbol>,
            name: &'a AstAssignIdent,
            kind: SymbolKind,
            resolve_docs: impl FnOnce() -> Option<DocMember>,
        ) {
            if !name.ident.starts_with('_') {
                result.entry(&name.ident).or_insert(Symbol {
                    name: name.ident.clone(),
                    detail: None,
                    span: Some(name.span),
                    kind,
                    doc: resolve_docs(),
                    param: None,
                });
            }
        }

        let mut last_node = None;
        for x in top_level_stmts(self.statement()) {
            match &**x {
                Stmt::Assign(assign) => {
                    assign.lhs.visit_lvalue(|name| {
                        let kind = SymbolKind::from_expr(&assign.rhs);
                        add(&mut result, name, kind, || {
                            last_node
                                .and_then(|last| get_doc_item_for_assign(last, &assign.lhs))
                                .map(DocMember::Property)
                        });
                    });
                }
                Stmt::AssignModify(dest, _, _) => {
                    dest.visit_lvalue(|name| {
                        add(&mut result, name, SymbolKind::Variable, || {
                            last_node
                                .and_then(|last| get_doc_item_for_assign(last, dest))
                                .map(DocMember::Property)
                        });
                    });
                }
                Stmt::Def(def) => {
                    let doc_item = get_doc_item_for_def(def);
                    add(
                        &mut result,
                        &def.name,
                        SymbolKind::Method {
                            arguments: def
                                .params
                                .iter()
                                .filter_map(|param| {
                                    MethodSymbolArgument::from_ast_parameter(
                                        param,
                                        doc_item.as_ref().and_then(|doc| {
                                            param.node.ident().and_then(|ident| {
                                                doc.find_param_with_name(&ident.ident)
                                            })
                                        }),
                                    )
                                })
                                .collect(),
                        },
                        || doc_item.map(DocMember::Function),
                    );
                }
                _ => {}
            }
            last_node = Some(x);
        }
        result.into_values().collect()
    }
}

#[cfg(test)]
mod tests {
    use starlark::syntax::Dialect;
    use starlark_syntax::slice_vec_ext::SliceExt;

    use super::*;

    fn module(x: &str) -> AstModule {
        AstModule::parse("X", x.to_owned(), &Dialect::Extended).unwrap()
    }

    #[test]
    fn test_lint_exported() {
        let modu = module(
            r#"
load("test", "a")
def b(): pass
d = 1
def _e(): pass
d = 2
"#,
        );
        let res = modu.exported_symbols();
        assert_eq!(
            res.map(|symbol| format!(
                "{} {}",
                modu.file_span(symbol.span.expect("span should be set")),
                symbol.name
            )),
            &["X:3:5-6 b", "X:4:1-2 d"]
        );
    }
}
