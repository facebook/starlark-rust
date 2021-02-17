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
    assert,
    syntax::{
        dialect::Dialect,
        lexer::{Lexer, Token, Token::*},
        testing::{assert_diagnostics, testcase_files},
    },
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
    Lexer::new(s, &Dialect::Standard, codemap.dupe(), file_span).for_each(|x| match x {
        Err(e) => diagnostics.push(e),
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
                IntegerLiteral(r) => Some(*r),
                Newline => None,
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
            Newline, Plus, Newline, Indent, Minus, Newline, Indent, Slash, Newline, Star, Newline,
            Dedent, Equal, Newline, Indent, Percent, Newline, Indent, Dot, Newline, Dedent, Dedent,
            Dedent, PlusEqual, Newline, Newline,
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
            Comma,
            Semicolon,
            Colon,
            PlusEqual,
            MinusEqual,
            StarEqual,
            SlashEqual,
            SlashSlashEqual,
            PercentEqual,
            EqualEqual,
            BangEqual,
            LessEqual,
            GreaterEqual,
            StarStar,
            Equal,
            LessThan,
            GreaterThan,
            Minus,
            Plus,
            Star,
            Percent,
            Slash,
            SlashSlash,
            Dot,
            OpeningCurly,
            ClosingCurly,
            OpeningSquare,
            ClosingSquare,
            OpeningRound,
            ClosingRound,
            Pipe,
            Newline,
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
            And, Else, Load, Break, For, Not, Not, In, Continue, If, Or, Def, In, Pass, Elif,
            Return, Lambda, Newline,
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
            IntegerLiteral(0),
            In,
            IntegerLiteral(1),
            And,
            IntegerLiteral(2),
            Else,
            IntegerLiteral(3),
            Load,
            IntegerLiteral(4),
            Break,
            IntegerLiteral(5),
            For,
            IntegerLiteral(6),
            Not,
            IntegerLiteral(7),
            Not,
            In,
            IntegerLiteral(8),
            Continue,
            IntegerLiteral(10),
            Identifier("identifier11".to_owned()),
            Newline,
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
            Reserved("as".to_owned()),
            Reserved("import".to_owned()),
            Reserved("is".to_owned()),
            Reserved("class".to_owned()),
            Reserved("nonlocal".to_owned()),
            Reserved("del".to_owned()),
            Reserved("raise".to_owned()),
            Reserved("except".to_owned()),
            Reserved("try".to_owned()),
            Reserved("finally".to_owned()),
            Reserved("while".to_owned()),
            Reserved("from".to_owned()),
            Reserved("with".to_owned()),
            Reserved("global".to_owned()),
            Reserved("yield".to_owned()),
            Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_comment() {
    // Comment should be ignored
    assert_eq!(collect_result("# a comment\n"), &[Newline]);
    assert_eq!(collect_result(" # a comment\n"), &[Newline]);
    let r = collect_result("a # a comment\n");
    assert_eq!(&[Identifier("a".to_owned()), Newline, Newline], &r[..]);
    // But it should not eat everything
    let r = collect_result("[\n# a comment\n]");
    assert_eq!(&[OpeningSquare, ClosingSquare, Newline,], &r[..]);
}

#[test]
fn test_identifier() {
    let r = collect_result("a identifier CAPS _CAPS _0123");
    assert_eq!(
        &[
            Identifier("a".to_owned()),
            Identifier("identifier".to_owned()),
            Identifier("CAPS".to_owned()),
            Identifier("_CAPS".to_owned()),
            Identifier("_0123".to_owned()),
            Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_string_lit() {
    let r = collect_result("'123' \"123\" '' \"\" '\\'' \"\\\"\" '\"' \"'\" '\\n' '\\w'");
    assert_eq!(
        &[
            StringLiteral("123".to_owned()),
            StringLiteral("123".to_owned()),
            StringLiteral("".to_owned()),
            StringLiteral("".to_owned()),
            StringLiteral("'".to_owned()),
            StringLiteral("\"".to_owned()),
            StringLiteral("\"".to_owned()),
            StringLiteral("'".to_owned()),
            StringLiteral("\n".to_owned()),
            StringLiteral("\\w".to_owned()),
            Newline,
        ],
        &r[..]
    );

    // unfinished string literal
    assert::parse_fail("!'!\n'");
    assert::parse_fail("!\"!\n\"");

    // Multiline string
    let r = collect_result("'''''' '''\\n''' '''\n''' \"\"\"\"\"\" \"\"\"\\n\"\"\" \"\"\"\n\"\"\"");
    assert_eq!(
        &[
            StringLiteral("".to_owned()),
            StringLiteral("\n".to_owned()),
            StringLiteral("\n".to_owned()),
            StringLiteral("".to_owned()),
            StringLiteral("\n".to_owned()),
            StringLiteral("\n".to_owned()),
            Newline,
        ],
        &r[..]
    );
    // Raw string
    let r = collect_result("r'' r\"\" r'\\'' r\"\\\"\" r'\"' r\"'\" r'\\n'");
    assert_eq!(
        &[
            StringLiteral("".to_owned()),
            StringLiteral("".to_owned()),
            StringLiteral("'".to_owned()),
            StringLiteral("\"".to_owned()),
            StringLiteral("\"".to_owned()),
            StringLiteral("'".to_owned()),
            StringLiteral("\\n".to_owned()),
            Newline,
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
            StringLiteral("A docstring.".to_owned()),
            Newline,
            Newline,
            Def,
            Identifier("_impl".to_owned()),
            OpeningRound,
            Identifier("ctx".to_owned()),
            ClosingRound,
            Colon,
            Newline,
            Indent,
            Identifier("print".to_owned()),
            OpeningRound,
            StringLiteral("Hello, World!".to_owned()),
            ClosingRound,
            Newline,
            Dedent,
            Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_escape_newline() {
    let r = collect_result("a \\\nb");
    assert_eq!(
        &[
            Identifier("a".to_owned()),
            Identifier("b".to_owned()),
            Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_lexer_multiline_triple() {
    let r = collect_result(
        r#"
cmd = """A \
    B \
    C \
    """"#,
    );
    assert_eq!(
        &[
            Newline,
            Identifier("cmd".to_owned()),
            Equal,
            StringLiteral("A     B     C     ".to_owned()),
            Newline,
        ],
        &r[..]
    );
}

#[test]
fn test_span() {
    let expected = vec![
        (0, Newline, 1),
        (1, Def, 4),
        (5, Identifier("test".to_owned()), 9),
        (9, OpeningRound, 10),
        (10, Identifier("a".to_owned()), 11),
        (11, ClosingRound, 12),
        (12, Colon, 13),
        (13, Newline, 14),
        (14, Indent, 16),
        (16, Identifier("fail".to_owned()), 20),
        (20, OpeningRound, 21),
        (21, Identifier("a".to_owned()), 22),
        (22, ClosingRound, 23),
        (23, Newline, 24),
        (24, Newline, 25),
        (25, Dedent, 25),
        (25, Identifier("test".to_owned()), 29),
        (29, OpeningRound, 30),
        (30, StringLiteral("abc".to_owned()), 35),
        (35, ClosingRound, 36),
        (36, Newline, 37),
        (37, Newline, 37),
    ];

    let mut codemap = CodeMap::new();
    let file = codemap.add_file(
        "x".to_owned(),
        r#"
def test(a):
  fail(a)

test("abc")
"#
        .to_owned(),
    );
    let actual: Vec<(u64, Token, u64)> = Lexer::new(
        file.source(),
        &Dialect::Standard,
        Arc::new(codemap),
        file.span,
    )
    .map(Result::unwrap)
    .collect();
    assert_eq!(expected, actual);
}

#[test]
fn test_lexer_final_comment() {
    let r = collect_result(
        r#"
x
# test"#,
    );
    assert_eq!(
        &[Newline, Identifier("x".to_owned()), Newline, Newline],
        &r[..]
    );
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
        Lexer::new(content, &Dialect::Standard, codemap.dupe(), file_span).for_each(|x| {
            if x.is_err() {
                diagnostics.push(x.err().unwrap());
            }
        });
    }
    assert_diagnostics(&diagnostics);
}
