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
    ast::Stmt,
    dialect::Dialect,
    grammar::StarlarkParser,
    lexer::Lexer,
    parse,
    parser::parse_error_add_span,
    testing::{assert_diagnostics, testcase_files},
};
use gazebo::prelude::*;
use std::sync::Arc;

fn unwrap_parse(e: &str) -> String {
    let mut codemap = codemap::CodeMap::new();
    let filespan = codemap.add_file("<test>".to_owned(), e.to_string()).span;
    let codemap = Arc::new(codemap);
    let lexer = Lexer::new(e, &Dialect::Standard, codemap.dupe(), filespan);
    match StarlarkParser::new().parse(&codemap, filespan, &Dialect::Extended, lexer) {
        Ok(x) => match x.node {
            Stmt::Statements(bv) => format!("{}", Stmt::Statements(bv)),
            y => panic!("Expected statements, got {:?}", y),
        },
        Err(e) => {
            assert_diagnostics(&[parse_error_add_span(e, filespan, codemap)]);
            panic!("Got errors!");
        }
    }
}

fn fails_parse(e: &str, dialect: &Dialect) {
    let mut codemap = codemap::CodeMap::new();
    let filespan = codemap.add_file("<test>".to_owned(), e.to_string()).span;
    let codemap = Arc::new(codemap);
    let lexer = Lexer::new(e, &Dialect::Standard, codemap.dupe(), filespan);
    match StarlarkParser::new().parse(&codemap, filespan, dialect, lexer) {
        Ok(x) => panic!("Expected failure, got {:?}", x),
        Err(_) => {}
    }
}

#[test]
fn test_empty() {
    assert!(unwrap_parse("\n").is_empty());
}

#[test]
fn test_top_level_comment() {
    assert!(unwrap_parse("# Test").is_empty());
}

#[test]
fn test_top_level_load() {
    assert!(!unwrap_parse("\nload(\"//top/level/load.bzl\", \"top-level\")\n").is_empty());
    assert!(!unwrap_parse("\nload(\"//top/level/load.bzl\", \"top-level\")").is_empty());
    assert!(
        !unwrap_parse("\nload(\n  \"//top/level/load.bzl\",\n  \"top-level\",\n)\n").is_empty()
    );
}

#[test]
fn test_top_level_assignation() {
    assert!(!unwrap_parse("\n_ASSIGNATION = 'top-level'\n").is_empty());
}

#[test]
fn test_top_level_docstring() {
    assert!(!unwrap_parse("\n\"\"\"Top-level docstring\"\"\"\n").is_empty());
}

#[test]
fn test_top_level_def() {
    assert_eq!(
        unwrap_parse("def toto():\n  pass\n"),
        "def toto():\n  pass\n"
    );
    fails_parse("def toto():\n  pass\n", &Dialect::Simple);
    // no new line at end of file
    assert_eq!(unwrap_parse("def toto():\n  pass"), "def toto():\n  pass\n");
    assert_eq!(
        unwrap_parse("def toto():\n  pass\ndef titi(): return 1"),
        "def toto():\n  pass\ndef titi():\n  return 1\n"
    );
    assert_eq!(
        unwrap_parse("def toto():\n  pass\n\ndef titi(): return 1"),
        "def toto():\n  pass\ndef titi():\n  return 1\n"
    );
    assert_eq!(unwrap_parse("def t():\n\n  pass"), "def t():\n  pass\n");
}

#[test]
fn test_top_level_def_with_docstring() {
    assert_eq!(
        unwrap_parse(
            "\"\"\"Top-level docstring\"\"\"

def toto():
  pass
"
        ),
        "\"Top-level docstring\"\ndef toto():\n  pass\n"
    );
}

#[test]
fn test_ifelse() {
    assert_eq!(
        unwrap_parse("def d():\n  if True:\n    a\n  else:\n    b"),
        "def d():\n  if True:\n    a\n  else:\n    b\n"
    );
}

#[test]
fn test_kwargs_passing() {
    assert_eq!(
        unwrap_parse("f(x, *a, **b); f(x, *a, **{a:b}); f(x, *[a], **b)"),
        "f(x, *a, **b)\nf(x, *a, **{a: b})\nf(x, *[a], **b)\n"
    );
}

#[test]
fn test_unary_op() {
    assert_eq!(unwrap_parse("a = -1"), "a = -1\n");
    assert_eq!(unwrap_parse("a = +1"), "a = +1\n");
    assert_eq!(unwrap_parse("a = -a"), "a = -a\n");
    assert_eq!(unwrap_parse("a = +a"), "a = +a\n");
}

#[test]
fn test_tuples() {
    assert_eq!(unwrap_parse("a = (-1)"), "a = -1\n"); // Not a tuple
    assert_eq!(unwrap_parse("a = (+1,)"), "a = (+1,)\n"); // But this is one
    assert_eq!(unwrap_parse("a = ()"), "a = ()\n");
}

#[test]
fn test_return() {
    assert_eq!(
        unwrap_parse("def fn(): return 1"),
        "def fn():\n  return 1\n"
    );
    assert_eq!(
        unwrap_parse("def fn(): return a()"),
        "def fn():\n  return a()\n"
    );
    assert_eq!(unwrap_parse("def fn(): return"), "def fn():\n  return\n");
}

// Regression test for https://github.com/google/starlark-rust/issues/44.
#[test]
fn test_optional_whitespace() {
    assert_eq!(unwrap_parse("6 or()"), "(6 or ())\n");
    assert_eq!(unwrap_parse("6or()"), "(6 or ())\n");
}

// Regression test for https://github.com/google/starlark-rust/issues/56.
#[test]
fn test_optional_whitespace_after_0() {
    assert_eq!(unwrap_parse("0in[1,2,3]"), "(0 in [1, 2, 3])\n");
}

#[test]
fn test_fncall_span() {
    let content = r#"def fn(a):
  fail(a)

fn(1)

fail(2)
"#;
    let mut codemap = codemap::CodeMap::new();
    let filespan = codemap
        .add_file("<test>".to_owned(), content.to_string())
        .span;
    let codemap = Arc::new(codemap);
    let lexer = Lexer::new(content, &Dialect::Standard, codemap.dupe(), filespan);
    match StarlarkParser::new().parse(&codemap, filespan, &Dialect::Extended, lexer) {
        Ok(x) => match x.node {
            Stmt::Statements(bv) => {
                let lines = bv.map(|x| codemap.look_up_pos(x.span.low()).position.line);
                assert_eq!(lines, vec![0, 3, 5])
            }
            y => panic!("Expected statements, got {:?}", y),
        },
        Err(e) => {
            assert_diagnostics(&[parse_error_add_span(e, filespan, codemap)]);
            panic!("Got errors!");
        }
    }
}

#[test]
fn test_comprehension() {
    assert_eq!(
        unwrap_parse("[x for x in range(12) if x % 2 == 0 if x % 3 == 0]"),
        "[x for x in range(12) if ((x % 2) == 0) if ((x % 3) == 0)]\n"
    );
}

#[test]
fn test_octal() {
    assert_eq!(unwrap_parse("0"), "0\n");
    assert_eq!(unwrap_parse("10"), "10\n");
    // Starlark requires us to ban leading zeros (confusion with implicit octal)
    fails_parse("01", &Dialect::Standard);
}

#[test]
fn test_lambda() {
    assert_eq!(
        unwrap_parse("x = lambda y: y + 1"),
        "x = (lambda y: (y + 1))\n"
    );
    fails_parse("x = lambda y: y + 1", &Dialect::Standard);
    assert_eq!(
        unwrap_parse("(lambda y: x == 1)(1)"),
        "(lambda y: (x == 1))(1)\n"
    );
    assert_eq!(
        unwrap_parse("(lambda x: x or 1)(1)"),
        "(lambda x: (x or 1))(1)\n"
    );
    assert_eq!(
        unwrap_parse("f = lambda x, y: x * y"),
        "f = (lambda x, y: (x * y))\n"
    );
    assert_eq!(unwrap_parse("lambda x: True"), "(lambda x: True)\n");
    assert_eq!(unwrap_parse("lambda: True"), "(lambda : True)\n");
    assert_eq!(
        unwrap_parse("f(lambda x, y=1, *args, **kwargs: x + y + z)"),
        "f((lambda x, y = 1, *args, **kwargs: ((x + y) + z)))\n"
    );
    assert_eq!(
        unwrap_parse("[x for x in [1, 2] if (lambda : 3 if True else 4)]"),
        "[x for x in [1, 2] if (lambda : (3 if True else 4))]\n"
    );
    // Note that Python3 and Go Starlark can both parse the line below,
    // but we can't, and the official Python3 grammar doesn't appear to be
    // able to either (we follow it in this position). Fortunately, its
    // a mostly meaningless program.
    // [x for x in [1, 2] if lambda : None]
}

#[test]
fn test_nested_def() {
    assert_eq!(
        unwrap_parse("def foo(x):\n  def bar(y): return y\n  return bar(x)"),
        "def foo(x):\n  def bar(y):\n    return y\n  return bar(x)\n"
    );
}

#[test]
fn smoke_test() {
    let mut diagnostics = Vec::new();
    for (file, content) in testcase_files() {
        if let Err(err) = parse(file, (*content).to_owned(), &Dialect::Extended) {
            diagnostics.push(err);
        }
    }
    assert_diagnostics(&diagnostics);
}
