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

use crate::codemap::{CodeMap, LineCol, Span, SpanLoc};
use gazebo::variants::VariantName;
use std::fmt::{self, Display};

pub(crate) trait LintWarning: Display + VariantName {
    fn is_serious(&self) -> bool;
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub struct LineCol1 {
    /// The line number within the file (1-indexed).
    pub line: usize,

    /// The column within the line (1-indexed).
    pub column: usize,
}

#[doc(hidden)] // Eventually we want CodeMap to gain these features, so this will go away
#[derive(Debug, Clone, Copy)]
pub struct LineColSpan {
    pub begin: LineCol1,
    pub end: LineCol1,
}

impl LineColSpan {
    pub fn spans_only_one_line(&self) -> bool {
        self.begin.line == self.end.line
    }

    pub fn is_empty_span(&self) -> bool {
        self.begin.line == self.end.line && self.begin.column == self.end.column
    }
}

impl Display for LineColSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty_span() {
            write!(f, "{}:{}", self.begin.line, self.begin.column)
        } else if self.spans_only_one_line() {
            write!(
                f,
                "{}:{}-{}",
                self.begin.line, self.begin.column, self.end.column
            )
        } else {
            write!(
                f,
                "{}:{}-{}:{}",
                self.begin.line, self.begin.column, self.end.line, self.end.column
            )
        }
    }
}

// Starlark line/columns are 0-based, then add 1 here to have 1-based.
impl LineColSpan {
    pub fn from_span_loc(span_loc: &SpanLoc) -> Self {
        Self::from_span(span_loc.begin, span_loc.end)
    }

    pub fn from_span(begin: LineCol, end: LineCol) -> Self {
        Self {
            begin: LineCol1 {
                line: begin.line + 1,
                column: begin.column + 1,
            },
            end: LineCol1 {
                line: end.line + 1,
                column: end.column + 1,
            },
        }
    }
}

#[derive(Debug)]
pub struct FileSpanLoc {
    pub path: String,
    pub span: LineColSpan,
}

impl FileSpanLoc {
    pub fn from_span_loc(span_loc: &SpanLoc) -> Self {
        Self {
            span: LineColSpan::from_span_loc(span_loc),
            path: span_loc.file.name().to_owned(),
        }
    }
}

impl Display for FileSpanLoc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.path, self.span)
    }
}

/// A private version of lint without the inner trait erased, useful so we can test
/// using full matching, but then erase the internal details when exporting to users.
pub(crate) struct LintT<T> {
    pub location: SpanLoc,
    pub original: String,
    pub problem: T,
}

/// A lint produced by the Starlark linter.
#[derive(Debug)]
pub struct Lint {
    /// Which code location does this lint refer to.
    pub location: SpanLoc,
    /// kebab-case constant describing this issue.
    pub short_name: String,
    /// Is this code highly-likely to be wrong, rather
    /// than merely stylistically non-ideal.
    pub serious: bool,
    /// The underlying problem.
    pub problem: String,
    /// The source at SpanLoc
    pub original: String,
}

impl Display for Lint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.problem)
    }
}

impl<T: Display> Display for LintT<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.problem)
    }
}

impl<T: LintWarning> LintT<T> {
    pub(crate) fn new(codemap: &CodeMap, span: Span, problem: T) -> Self {
        let location = codemap.look_up_span(span);
        Self {
            original: location.file.source_slice(span).to_owned(),
            location,
            problem,
        }
    }

    pub(crate) fn erase(self) -> Lint {
        Lint {
            location: self.location,
            short_name: kebab(self.problem.variant_name()),
            serious: self.problem.is_serious(),
            problem: self.problem.to_string(),
            original: self.original,
        }
    }
}

fn kebab(xs: &str) -> String {
    let mut res = String::new();
    for x in xs.chars() {
        if x.is_uppercase() {
            if !res.is_empty() {
                res.push('-');
            }
            for y in x.to_lowercase() {
                res.push(y);
            }
        } else {
            res.push(x);
        }
    }
    res
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lint_kebab() {
        assert_eq!(kebab("Unreachable"), "unreachable");
        assert_eq!(kebab("UsingIgnored"), "using-ignored");
        assert_eq!(
            kebab("MissingReturnExpression"),
            "missing-return-expression"
        );
        assert_eq!(
            kebab("DuplicateTopLevelAssign"),
            "duplicate-top-level-assign"
        );
    }

    #[test]
    fn test_line_col_span_display_point() {
        let line_col = LineCol { line: 0, column: 0 };
        let span = LineColSpan::from_span(line_col, line_col);
        assert_eq!(span.to_string(), "1:1");
    }

    #[test]
    fn test_line_col_span_display_single_line_span() {
        let begin = LineCol { line: 0, column: 0 };
        let end = LineCol {
            line: 0,
            column: 32,
        };
        let span = LineColSpan::from_span(begin, end);
        assert_eq!(span.to_string(), "1:1-33");
    }

    #[test]
    fn test_line_col_span_display_multi_line_span() {
        let begin = LineCol { line: 0, column: 0 };
        let end = LineCol {
            line: 2,
            column: 32,
        };
        let span = LineColSpan::from_span(begin, end);
        assert_eq!(span.to_string(), "1:1-3:33");
    }
}
