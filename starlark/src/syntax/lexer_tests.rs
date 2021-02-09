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

use crate::syntax::{
    dialect::Dialect,
    lexer::{Lexer, LexerError, Token},
    testing::{assert_diagnostics, testcase_files},
};
use codemap::CodeMap;
use gazebo::prelude::*;
use std::sync::Arc;

fn collect_result(s: &'static str) -> Vec<Token> {
    let mut codemap = CodeMap::new();
    let mut diagnostics = Vec::new();
    let mut result = Vec::new();
    let file_span = codemap.add_file("<test>".to_owned(), s.to_owned()).span;
    let mut pos = 0;
    let codemap = Arc::new(codemap);
    Lexer::new(s, &Dialect::Standard).for_each(|x| match x {
        Err(e) => diagnostics.push(e.add_span(file_span, codemap.dupe()).into()),
        Ok((i, t, j)) => {
            let span_incorrect = format!("Span of {:?} incorrect", t);
            assert!(pos <= i, "{}: {} > {}", span_incorrect, pos, i);
            result.push(t);
            assert!(i <= j, "{}: {} > {}", span_incorrect, i, j);
            pos = j;
        }
    });
    assert_diagnostics(&diagnostics);
    result
}

#[test]
fn test_int_lit() {
    let get_result = |s: &'static str| -> Vec<i32> {
        collect_result(s)
            .iter()
            .filter_map(|v| match v {
                Token::IntegerLiteral(r) => Some(*r),
                Token::Newline => None,
                _ => panic!("{:?} is not a integer literal", v),
            })
            .collect()
    };
    assert_eq!(vec![0, 123], get_result("0 123"));
    assert_eq!(vec![0x7f, 0x7f], get_result("0x7F 0x7f"));
    assert_eq!(vec![0b1011, 0b1011], get_result("0B1011 0b1011"));
    assert_eq!(vec![0o755, 0o755], get_result("0o755 0O755"));
}

#[test]
fn test_indentation() {
    let r = collect_result(
        "
+
  -
      /
      *
  =
    %
      .
+=
",
    );
    assert_eq!(
        &[
            Token::Newline,
            Token::Plus,
            Token::Newline,
            Token::Indent,
            Token::Minus,
            Token::Newline,
            Token::Indent,
            Token::Slash,
            Token::Newline,
            Token::Star,
            Token::Newline,
            Token::Dedent,
            Token::Equal,
            Token::Newline,
            Token::Indent,
            Token::Percent,
            Token::Newline,
            Token::Indent,
            Token::Dot,
            Token::Newline,
            Token::Dedent,
            Token::Dedent,
            Token::Dedent,
            Token::PlusEqual,
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_symbols() {
    let r = collect_result(
        ", ; : += -= *= /= //= %= == != <= >= ** = < > - + * % / // . { } [ ] ( ) |",
    );
    assert_eq!(
        &[
            Token::Comma,
            Token::Semicolon,
            Token::Colon,
            Token::PlusEqual,
            Token::MinusEqual,
            Token::StarEqual,
            Token::SlashEqual,
            Token::DoubleSlashEqual,
            Token::PercentEqual,
            Token::DoubleEqual,
            Token::BangEqual,
            Token::LessEqual,
            Token::GreaterEqual,
            Token::DoubleStar,
            Token::Equal,
            Token::LessThan,
            Token::GreaterThan,
            Token::Minus,
            Token::Plus,
            Token::Star,
            Token::Percent,
            Token::Slash,
            Token::DoubleSlash,
            Token::Dot,
            Token::OpeningCurly,
            Token::ClosingCurly,
            Token::OpeningSquare,
            Token::ClosingSquare,
            Token::OpeningRound,
            Token::ClosingRound,
            Token::Pipe,
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_keywords() {
    let r = collect_result(
        "and else load break for not not  in continue if or def in pass elif return lambda",
    );
    assert_eq!(
        &[
            Token::And,
            Token::Else,
            Token::Load,
            Token::Break,
            Token::For,
            Token::Not,
            Token::Not,
            Token::In,
            Token::Continue,
            Token::If,
            Token::Or,
            Token::Def,
            Token::In,
            Token::Pass,
            Token::Elif,
            Token::Return,
            Token::Lambda,
            Token::Newline,
        ],
        &r[..]
    );
}

// Regression test for https://github.com/google/starlark-rust/issues/44.
#[test]
fn test_number_collated_with_keywords_or_identifier() {
    let r =
        collect_result("0in 1and 2else 3load 4break 5for 6not 7not  in 8continue 10identifier11");
    assert_eq!(
        &[
            Token::IntegerLiteral(0),
            Token::In,
            Token::IntegerLiteral(1),
            Token::And,
            Token::IntegerLiteral(2),
            Token::Else,
            Token::IntegerLiteral(3),
            Token::Load,
            Token::IntegerLiteral(4),
            Token::Break,
            Token::IntegerLiteral(5),
            Token::For,
            Token::IntegerLiteral(6),
            Token::Not,
            Token::IntegerLiteral(7),
            Token::Not,
            Token::In,
            Token::IntegerLiteral(8),
            Token::Continue,
            Token::IntegerLiteral(10),
            Token::Identifier("identifier11".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_reserved() {
    let r = collect_result(
        "as import is class nonlocal del raise except try finally \
             while from with global yield",
    );
    assert_eq!(
        &[
            Token::Reserved("as".to_owned()),
            Token::Reserved("import".to_owned()),
            Token::Reserved("is".to_owned()),
            Token::Reserved("class".to_owned()),
            Token::Reserved("nonlocal".to_owned()),
            Token::Reserved("del".to_owned()),
            Token::Reserved("raise".to_owned()),
            Token::Reserved("except".to_owned()),
            Token::Reserved("try".to_owned()),
            Token::Reserved("finally".to_owned()),
            Token::Reserved("while".to_owned()),
            Token::Reserved("from".to_owned()),
            Token::Reserved("with".to_owned()),
            Token::Reserved("global".to_owned()),
            Token::Reserved("yield".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_comment() {
    // Comment should be ignored
    assert!(collect_result("# a comment\n").is_empty());
    assert!(collect_result(" # a comment\n").is_empty());
    let r = collect_result("a # a comment\n");
    assert_eq!(&[Token::Identifier("a".to_owned()), Token::Newline], &r[..]);
    // But it should not eat everything
    let r = collect_result("[\n# a comment\n]");
    assert_eq!(
        &[Token::OpeningSquare, Token::ClosingSquare, Token::Newline],
        &r[..]
    );
}

#[test]
fn test_identifier() {
    let r = collect_result("a identifier CAPS _CAPS _0123");
    assert_eq!(
        &[
            Token::Identifier("a".to_owned()),
            Token::Identifier("identifier".to_owned()),
            Token::Identifier("CAPS".to_owned()),
            Token::Identifier("_CAPS".to_owned()),
            Token::Identifier("_0123".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_string_lit() {
    let r = collect_result("'123' \"123\" '' \"\" '\\'' \"\\\"\" '\"' \"'\" '\\n' '\\w'");
    assert_eq!(
        &[
            Token::StringLiteral("123".to_owned()),
            Token::StringLiteral("123".to_owned()),
            Token::StringLiteral("".to_owned()),
            Token::StringLiteral("".to_owned()),
            Token::StringLiteral("'".to_owned()),
            Token::StringLiteral("\"".to_owned()),
            Token::StringLiteral("\"".to_owned()),
            Token::StringLiteral("'".to_owned()),
            Token::StringLiteral("\n".to_owned()),
            Token::StringLiteral("\\w".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );

    // unfinished string literal
    assert_eq!(
        Lexer::new("'\n'", &Dialect::Standard).next().unwrap(),
        Err(LexerError::UnfinishedStringLiteral(0, 1))
    );
    assert_eq!(
        Lexer::new("\"\n\"", &Dialect::Standard).next().unwrap(),
        Err(LexerError::UnfinishedStringLiteral(0, 1))
    );
    // Multiline string
    let r = collect_result("'''''' '''\\n''' '''\n''' \"\"\"\"\"\" \"\"\"\\n\"\"\" \"\"\"\n\"\"\"");
    assert_eq!(
        &[
            Token::StringLiteral("".to_owned()),
            Token::StringLiteral("\n".to_owned()),
            Token::StringLiteral("\n".to_owned()),
            Token::StringLiteral("".to_owned()),
            Token::StringLiteral("\n".to_owned()),
            Token::StringLiteral("\n".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );
    // Raw string
    let r = collect_result("r'' r\"\" r'\\'' r\"\\\"\" r'\"' r\"'\" r'\\n'");
    assert_eq!(
        &[
            Token::StringLiteral("".to_owned()),
            Token::StringLiteral("".to_owned()),
            Token::StringLiteral("'".to_owned()),
            Token::StringLiteral("\"".to_owned()),
            Token::StringLiteral("\"".to_owned()),
            Token::StringLiteral("'".to_owned()),
            Token::StringLiteral("\\n".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_simple_example() {
    let r = collect_result(
        "\"\"\"A docstring.\"\"\"

def _impl(ctx):
  # Print Hello, World!
  print('Hello, World!')
",
    );
    assert_eq!(
        &[
            Token::StringLiteral("A docstring.".to_owned()),
            Token::Newline,
            Token::Newline,
            Token::Def,
            Token::Identifier("_impl".to_owned()),
            Token::OpeningRound,
            Token::Identifier("ctx".to_owned()),
            Token::ClosingRound,
            Token::Colon,
            Token::Newline,
            Token::Indent,
            Token::Identifier("print".to_owned()),
            Token::OpeningRound,
            Token::StringLiteral("Hello, World!".to_owned()),
            Token::ClosingRound,
            Token::Newline,
            Token::Dedent,
        ],
        &r[..]
    );
}

#[test]
fn test_escape_newline() {
    let r = collect_result("a \\\nb");
    assert_eq!(
        &[
            Token::Identifier("a".to_owned()),
            Token::Identifier("b".to_owned()),
            Token::Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_span() {
    let expected = vec![
        (0, Token::Newline, 1),
        (1, Token::Def, 4),
        (5, Token::Identifier("test".to_owned()), 9),
        (9, Token::OpeningRound, 10),
        (10, Token::Identifier("a".to_owned()), 11),
        (11, Token::ClosingRound, 12),
        (12, Token::Colon, 13),
        (13, Token::Newline, 14),
        (14, Token::Indent, 16),
        (16, Token::Identifier("fail".to_owned()), 20),
        (20, Token::OpeningRound, 21),
        (21, Token::Identifier("a".to_owned()), 22),
        (22, Token::ClosingRound, 23),
        (23, Token::Newline, 24),
        (24, Token::Newline, 25),
        (25, Token::Dedent, 25),
        (25, Token::Identifier("test".to_owned()), 29),
        (29, Token::OpeningRound, 30),
        (30, Token::StringLiteral("abc".to_owned()), 35),
        (35, Token::ClosingRound, 36),
        (36, Token::Newline, 37),
    ];
    let actual: Vec<(u64, Token, u64)> = Lexer::new(
        r#"
def test(a):
  fail(a)

test("abc")
"#,
        &Dialect::Standard,
    )
    .map(Result::unwrap)
    .collect();
    assert_eq!(expected, actual);
}

#[test]
fn smoke_test() {
    let mut diagnostics = Vec::new();
    for (file, content) in testcase_files() {
        let mut codemap = codemap::CodeMap::new();
        let file_span = codemap
            .add_file((*file).to_owned(), (*content).to_owned())
            .span;
        let codemap = Arc::new(codemap);
        Lexer::new(content, &Dialect::Standard).for_each(|x| {
            if x.is_err() {
                diagnostics.push(x.err().unwrap().add_span(file_span, codemap.dupe()).into());
            }
        });
    }
    assert_diagnostics(&diagnostics);
}
