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

use crate::{
    analysis::bind::{Bind, Scope},
    codemap::{Pos, ResolvedSpan, Span},
    syntax::AstModule,
};

impl AstModule {
    /// Attempts to find the location where a symbol is defined in the module, or `None` if it
    /// was not defined anywhere in this file.
    ///
    /// `line` and `col` are zero based indexes of a location of the symbol to attempt to lookup.
    ///
    /// This method also handles scoping properly (i.e. an access of "foo" in a function
    /// will return location of the parameter "foo", even if there is a global called "foo").
    pub fn find_definition(&self, line: u32, col: u32) -> Option<ResolvedSpan> {
        enum DefinitionLocation<'a> {
            // The location of the definition of the symbol at the current line/column
            Location(Span),
            // The definition was not found in the current scope but the name of an identifier
            // was found at the given position. This should be checked in outer scopes
            // to attempt to find the definition.
            Name(&'a str),
            // None of the accesses matched the position that was provided.
            NotFound,
        }

        // Look at the given scope and child scopes to try to find the definition of the symbol
        // accessed at Pos.
        fn find_definition_in_scope<'a>(scope: &'a Scope, pos: Pos) -> DefinitionLocation<'a> {
            for bind in &scope.inner {
                match bind {
                    Bind::Set(_, _) => {}
                    Bind::Get(g) => {
                        if g.span.begin() <= pos && pos <= g.span.end() {
                            let res = match scope.bound.get(g.node.as_str()) {
                                Some((_, span)) => DefinitionLocation::Location(*span),
                                // We know the symbol name, but it might only be available in
                                // an outer scope.
                                None => DefinitionLocation::Name(g.node.as_str()),
                            };
                            return res;
                        }
                    }
                    Bind::Flow => {}
                    Bind::Scope(inner_scope) => match find_definition_in_scope(inner_scope, pos) {
                        DefinitionLocation::Location(span) => {
                            return DefinitionLocation::Location(span);
                        }
                        DefinitionLocation::Name(missing_symbol) => {
                            return match scope.bound.get(missing_symbol) {
                                None => DefinitionLocation::Name(missing_symbol),
                                Some((_, span)) => DefinitionLocation::Location(*span),
                            };
                        }
                        DefinitionLocation::NotFound => {}
                    },
                }
            }
            DefinitionLocation::NotFound
        }

        let scope = crate::analysis::bind::scope(self);
        let line_span = self.codemap.line_span(line as usize);
        let current_pos = std::cmp::min(line_span.begin() + col, line_span.end());

        match find_definition_in_scope(&scope, current_pos) {
            DefinitionLocation::Location(span) => Some(self.codemap.resolve_span(span)),
            DefinitionLocation::Name(missing_symbol) => scope
                .bound
                .get(missing_symbol)
                .map(|(_, span)| self.codemap.resolve_span(*span)),
            DefinitionLocation::NotFound => None,
        }
    }
}

#[cfg(test)]
mod test {
    use textwrap::dedent;

    use crate::{
        codemap::ResolvedSpan,
        syntax::{AstModule, Dialect},
    };

    #[test]
    fn finds_local_definitions() {
        let contents = dedent(
            r#"
        load("bar.star", "print");

        x = 1
        y = 2

        def add(y: "int"):
            return x + y

        def invalid_symbol():
            return y + z

        print(x)
        add(3)
        invalid_symbol()
        "#,
        )
        .trim()
        .to_owned();
        let module = AstModule::parse("foo.star", contents, &Dialect::Extended).unwrap();

        // Call of the "print" function
        let expected = Some(ResolvedSpan {
            begin_line: 0,
            begin_column: 17,
            end_line: 0,
            end_column: 24,
        });
        assert_eq!(expected, module.find_definition(11, 0));
        assert_eq!(expected, module.find_definition(11, 2));
        assert_eq!(expected, module.find_definition(11, 4));

        // The "x" in the "print()" call
        let expected = Some(ResolvedSpan {
            begin_line: 2,
            begin_column: 0,
            end_line: 2,
            end_column: 1,
        });
        assert_eq!(expected, module.find_definition(11, 6));

        // The call to "add"
        let expected = Some(ResolvedSpan {
            begin_line: 5,
            begin_column: 4,
            end_line: 5,
            end_column: 7,
        });
        assert_eq!(expected, module.find_definition(12, 0));
        assert_eq!(expected, module.find_definition(12, 1));
        assert_eq!(expected, module.find_definition(12, 2));

        // The call to "invalid_symbol"
        let expected = Some(ResolvedSpan {
            begin_line: 8,
            begin_column: 4,
            end_line: 8,
            end_column: 18,
        });
        assert_eq!(expected, module.find_definition(13, 0));
        assert_eq!(expected, module.find_definition(13, 2));
        assert_eq!(expected, module.find_definition(13, 13));

        // Within "add", get the global "x", and the locally scoped "y"
        let expected_x = Some(ResolvedSpan {
            begin_line: 2,
            begin_column: 0,
            end_line: 2,
            end_column: 1,
        });
        let expected_y = Some(ResolvedSpan {
            begin_line: 5,
            begin_column: 8,
            end_line: 5,
            end_column: 9,
        });
        assert_eq!(expected_x, module.find_definition(6, 11));
        assert_eq!(expected_y, module.find_definition(6, 15));

        // Within the "invalid_symbol" function, return None for "z" and the global "y" for "y"
        let expected_y = Some(ResolvedSpan {
            begin_line: 3,
            begin_column: 0,
            end_line: 3,
            end_column: 1,
        });
        assert_eq!(expected_y, module.find_definition(9, 11));
        assert_eq!(None, module.find_definition(9, 15));

        // The "return" of "add" should be None as it's not an identifier / access
        assert_eq!(None, module.find_definition(12, 6));
    }
}
