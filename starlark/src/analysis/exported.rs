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

use crate::codemap::FileSpan;
use crate::collections::SmallMap;
use crate::syntax::ast::AstAssignIdentP;
use crate::syntax::ast::AstExprP;
use crate::syntax::ast::AstNoPayload;
use crate::syntax::ast::DefP;
use crate::syntax::ast::ExprP;
use crate::syntax::ast::Stmt;
use crate::syntax::AstModule;

#[derive(Debug)]
pub enum ExportedSymbolKind {
    Variable,
    Method,
}

#[derive(Debug)]
pub struct ExportedSymbol<'a> {
    pub name: &'a str,
    pub span: FileSpan,
    pub kind: ExportedSymbolKind,
}

impl AstModule {
    /// Which symbols are exported by this module. These are the top-level assignments,
    /// including function definitions. Any symbols that start with `_` are not exported.
    pub fn exported_symbols(&self) -> Vec<ExportedSymbol> {
        // Map since we only want to store the first of each export
        // IndexMap since we want the order to match the order they were defined in
        let mut result: SmallMap<&str, _> = SmallMap::new();
        for x in self.top_level_statements() {
            match &**x {
                Stmt::Assign(dest, rhs) => {
                    let source = &rhs.as_ref().1;
                    dest.visit_lvalue(|name| {
                        result
                            .entry(&name.0)
                            .or_insert(self.get_exported_symbol_from_assignment(name, source));
                    });
                }
                Stmt::AssignModify(dest, _, source) => {
                    dest.visit_lvalue(|name| {
                        result
                            .entry(&name.0)
                            .or_insert(self.get_exported_symbol_from_assignment(name, source));
                    });
                }
                Stmt::Def(DefP { name, .. }) => {
                    result.entry(&name.0).or_insert(ExportedSymbol {
                        name: &name.0,
                        span: self.file_span(name.span),
                        kind: ExportedSymbolKind::Method,
                    });
                }
                _ => {}
            }
        }
        result
            .into_iter()
            .filter(|(name, _)| !name.starts_with('_'))
            .map(|(_, exported_symbol)| exported_symbol)
            .collect()
    }

    /// Construct an [`ExportedSymbol`] based on the given assignment components.
    fn get_exported_symbol_from_assignment<'a>(
        &self,
        name: &'a AstAssignIdentP<AstNoPayload>,
        source: &AstExprP<AstNoPayload>,
    ) -> ExportedSymbol<'a> {
        ExportedSymbol {
            name: &name.0,
            span: self.file_span(name.span),
            kind: match source.node {
                ExprP::Lambda(_) => ExportedSymbolKind::Method,
                _ => ExportedSymbolKind::Variable,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use gazebo::prelude::*;

    use super::*;
    use crate::syntax::Dialect;

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
            res.map(|symbol| format!("{} {}", symbol.span, symbol.name)),
            &["X:3:5-6 b", "X:4:1-2 d"]
        );
    }
}
