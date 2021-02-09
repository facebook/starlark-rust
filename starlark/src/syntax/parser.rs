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

use crate::{
    errors::Diagnostic,
    syntax::{
        ast::{AstModule, AstStmt, Stmt},
        dialect::Dialect,
        grammar::StarlarkParser,
        lexer::{Lexer, LexerError, Token},
    },
};
use codemap::{CodeMap, Span, SpanLoc};
use lalrpop_util as lu;
use std::{fs, path::Path, sync::Arc};

fn one_of(expected: &[String]) -> String {
    let mut result = String::new();
    for (i, e) in expected.iter().enumerate() {
        let sep = match i {
            0 => "one of",
            _ if i < expected.len() - 1 => ",",
            // Last expected message to be written
            _ => " or",
        };
        result.push_str(&format!("{} {}", sep, e));
    }
    result
}

/// Convert the error to a codemap diagnostic.
///
/// To build this diagnostic, the method needs the file span corresponding
/// to the parsed file.
pub(crate) fn parse_error_add_span(
    err: lu::ParseError<u64, Token, LexerError>,
    span: Span,
    codemap: Arc<CodeMap>,
) -> Diagnostic {
    let message = match &err {
        lu::ParseError::InvalidToken { .. } => "Parse error: invalid token".to_owned(),
        lu::ParseError::UnrecognizedToken {
            token: (_x, Token::Reserved(s), _y),
            expected: _unused,
        } => format!("Parse error: cannot use reserved keyword `{}`", s),
        lu::ParseError::ExtraToken {
            token: (_x, Token::Reserved(s), _y),
        } => format!("Parse error: cannot use reserved keyword `{}`", s),
        lu::ParseError::UnrecognizedToken {
            token: (_x, t, ..),
            expected,
        } => format!(
            "Parse error: unexpected {} here, expected {}",
            t,
            one_of(expected)
        ),
        lu::ParseError::ExtraToken { token: (_x, t, ..) } => {
            format!("Parse error: extraneous token {}", t)
        }
        lu::ParseError::UnrecognizedEOF { .. } => "Parse error: unexpected end of file".to_owned(),
        lu::ParseError::User { error } => return error.add_span(span, codemap),
    };
    let span = match &err {
        lu::ParseError::InvalidToken { location } => span.subspan(*location, *location),
        lu::ParseError::UnrecognizedToken {
            token: (x, .., y), ..
        } => span.subspan(*x, *y),
        lu::ParseError::UnrecognizedEOF { .. } => {
            let x = span.high() - span.low();
            span.subspan(x, x)
        }
        lu::ParseError::ExtraToken { token: (x, .., y) } => span.subspan(*x, *y),
        lu::ParseError::User { .. } => unreachable!(),
    };

    let mut e = Diagnostic::new(message);
    e.set_span(span, codemap);
    e
}

/// Parse a build file (if build is true) or a starlark file provided as a
/// content using a custom lexer.
///
/// # arguments
///
/// * codemap: the codemap object used for diagnostics
/// * filename: the name of the file being parsed, for diagnostics
/// * content: the content to parse
/// * dialect: starlark language dialect
/// * lexer: the lexer to use for parsing
pub(crate) fn parse_lexer(
    filename: &str,
    content: &str,
    dialect: &Dialect,
    lexer: Lexer,
) -> anyhow::Result<AstModule> {
    let mut codemap = CodeMap::new();
    let filespan = codemap
        .add_file(filename.to_string(), content.to_string())
        .span;
    match StarlarkParser::new().parse(filespan, dialect, lexer) {
        Ok(v) => Ok(AstModule::create(codemap, v)?),
        Err(p) => Err(parse_error_add_span(p, filespan, Arc::new(codemap)).into()),
    }
}

impl AstModule {
    fn create(codemap: CodeMap, statement: AstStmt) -> anyhow::Result<AstModule> {
        let codemap = Arc::new(codemap);
        Stmt::validate_break_continue(&codemap, &statement)?;
        Ok(AstModule { codemap, statement })
    }

    pub fn collect_loads(&self) -> Vec<&str> {
        fn f<'a>(ast: &'a AstStmt, vec: &mut Vec<&'a str>) {
            match &ast.node {
                Stmt::Load(module, ..) => vec.push(&module.node),
                Stmt::Statements(stmts) => {
                    for s in stmts {
                        f(s, vec);
                    }
                }
                _ => {}
            }
        }

        let mut loads = Vec::new();
        f(&self.statement, &mut loads);
        loads
    }

    pub fn look_up_span(&self, x: Span) -> SpanLoc {
        self.codemap.look_up_span(x)
    }
}

/// Parse a build file (if build is true) or a starlark file provided as a
/// content.
///
/// # arguments
///
/// * codemap: the codemap object used for diagnostics
/// * filename: the name of the file being parsed, for diagnostics
/// * content: the content to parse
/// * dialect: starlark language dialect.
pub fn parse(filename: &str, content: &str, dialect: &Dialect) -> anyhow::Result<AstModule> {
    parse_lexer(filename, content, dialect, Lexer::new(content, dialect))
}

/// Parse a build file (if build is true) or a starlark file, reading the
/// content from the file system.
///
/// # arguments
///
/// * codemap: the codemap object used for diagnostics
/// * path: the path to the file to parse
/// * dialect: starlark language dialect
///
/// # Note
///
/// This method unwrap the path to a unicode string, which can panic.
pub fn parse_file(path: &Path, dialect: &Dialect) -> anyhow::Result<AstModule> {
    let content = fs::read_to_string(path)?;
    parse(&path.to_string_lossy(), &content, dialect)
}
