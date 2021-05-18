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

//! A data structure for tracking source positions in language implementations
//! The `CodeMap` tracks all source files and maps positions within them to linear indexes as if all
//! source files were concatenated. This allows a source position to be represented by a small
//! 32-bit `Pos` indexing into the `CodeMap`, under the assumption that the total amount of parsed
//! source code will not exceed 4GiB. The `CodeMap` can look up the source file, line, and column
//! of a `Pos` or `Span`, as well as provide source code snippets for error reporting.
//!
//! # Example
//! ```
//! use starlark::codemap::CodeMap;
//! let mut codemap = CodeMap::new("test.rs".to_owned(), "fn test(){\n    println!(\"Hello\");\n}\n".to_owned());
//! let string_literal_span = codemap.file_span().subspan(24, 31);
//!
//! let location = codemap.look_up_span(string_literal_span);
//! assert_eq!(location.file.name(), "test.rs");
//! assert_eq!(location.begin.line, 1);
//! assert_eq!(location.begin.column, 13);
//! assert_eq!(location.end.line, 1);
//! assert_eq!(location.end.column, 20);
//! ```
use gazebo::prelude::*;
use std::{
    cmp,
    fmt::{self, Display},
    hash::Hash,
    ops::{Add, Deref, Sub},
    sync::Arc,
};

/// A small, `Copy`, value representing a position in a `CodeMap`'s file.
#[derive(
    Copy, Clone, Dupe, Hash, Eq, PartialEq, Ord, PartialOrd, Debug, Default
)]
pub struct Pos(u32);

impl Add<u32> for Pos {
    type Output = Pos;
    fn add(self, other: u32) -> Pos {
        Pos(self.0 + other)
    }
}

impl Sub<Pos> for Pos {
    type Output = u32;
    fn sub(self, other: Pos) -> u32 {
        self.0 - other.0
    }
}

/// A range of text within a CodeMap.
#[derive(Copy, Dupe, Clone, Hash, Eq, PartialEq, Debug, Default)]
pub struct Span {
    /// The position in the codemap representing the first byte of the span.
    low: Pos,

    /// The position after the last byte of the span.
    high: Pos,
}

impl Span {
    /// Makes a span from offsets relative to the start of this span.
    ///
    /// # Panics
    ///   * If `end < begin`
    ///   * If `end` is beyond the length of the span
    pub fn subspan(self, begin: u32, end: u32) -> Span {
        assert!(end >= begin);
        assert!(self.low + end <= self.high);
        Span {
            low: self.low + begin,
            high: self.low + end,
        }
    }

    /// Checks if a span is contained within this span.
    pub fn contains(self, other: Span) -> bool {
        self.low <= other.low && self.high >= other.high
    }

    /// The position in the codemap representing the first byte of the span.
    pub fn low(self) -> Pos {
        self.low
    }

    /// The position after the last byte of the span.
    pub fn high(self) -> Pos {
        self.high
    }

    /// The length in bytes of the text of the span
    pub fn len(self) -> u32 {
        self.high - self.low
    }

    /// Create a span that encloses both `self` and `other`.
    pub fn merge(self, other: Span) -> Span {
        Span {
            low: cmp::min(self.low, other.low),
            high: cmp::max(self.high, other.high),
        }
    }
}

/// Associate a Span with a value of arbitrary type (e.g. an AST node).
#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.node
    }
}

/// A data structure recording a source code file for position lookup.
#[derive(Clone, Dupe)]
pub struct CodeMap {
    file: Arc<File>,
}

impl Default for CodeMap {
    fn default() -> Self {
        Self::new("".to_owned(), "".to_owned())
    }
}

impl fmt::Debug for CodeMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "CodeMap({:?})", self.file.name)
    }
}

impl PartialEq for CodeMap {
    /// Compares by identity
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.file, &other.file)
    }
}

impl Eq for CodeMap {}

impl CodeMap {
    /// Creates an new `CodeMap`.
    pub fn new(filename: String, contents: String) -> CodeMap {
        let mut lines = vec![Pos(0)];
        lines.extend(contents.match_indices('\n').map(|(p, _)| Pos(p as u32 + 1)));

        CodeMap {
            file: Arc::new(File {
                name: filename,
                source: contents,
                lines,
            }),
        }
    }

    /// Looks up a `File`
    pub(crate) fn get_file(&self) -> &Arc<File> {
        &self.file
    }

    pub fn file_span(&self) -> Span {
        Span {
            low: Pos(0),
            high: Pos(self.file.source.len() as u32),
        }
    }

    /// Gets the file and its line and column ranges represented by a `Span`.
    pub fn look_up_span(&self, span: Span) -> SpanLoc {
        let begin = self.find_line_col(span.low);
        let end = self.find_line_col(span.high);
        SpanLoc {
            file: self.dupe(),
            begin,
            end,
        }
    }
}

/// A `CodeMap`'s record of a source file.
pub(crate) struct File {
    /// The filename as it would be displayed in an error message.
    name: String,

    /// Contents of the file.
    source: String,

    /// Byte positions of line beginnings.
    lines: Vec<Pos>,
}

impl CodeMap {
    /// Gets the name of the file
    pub fn name(&self) -> &str {
        &self.file.name
    }

    /// Gets the line number of a Pos.
    ///
    /// The lines are 0-indexed (first line is numbered 0)
    ///
    /// # Panics
    ///
    ///  * If `pos` is not within this file's span
    pub fn find_line(&self, pos: Pos) -> usize {
        assert!(pos <= self.file_span().high());
        match self.file.lines.binary_search(&pos) {
            Ok(i) => i,
            Err(i) => i - 1,
        }
    }

    /// Gets the line and column of a Pos.
    ///
    /// # Panics
    ///
    /// * If `pos` is not with this file's span
    /// * If `pos` points to a byte in the middle of a UTF-8 character
    pub fn find_line_col(&self, pos: Pos) -> LineCol {
        let line = self.find_line(pos);
        let line_span = self.line_span(line);
        let byte_col = pos - line_span.low;
        let column = self.source_slice(line_span)[..byte_col as usize]
            .chars()
            .count();

        LineCol { line, column }
    }

    /// Gets the full source text of the file
    pub fn source(&self) -> &str {
        &self.file.source
    }

    /// Gets the source text of a Span.
    ///
    /// # Panics
    ///
    ///   * If `span` is not entirely within this file.
    pub fn source_slice(&self, span: Span) -> &str {
        assert!(self.file_span().contains(span));
        &self.file.source[(span.low.0 as usize)..(span.high.0 as usize)]
    }

    /// Gets the span representing a line by line number.
    ///
    /// The line number is 0-indexed (first line is numbered 0). The returned span includes the
    /// line terminator.
    ///
    /// # Panics
    ///
    ///  * If the line number is out of range
    pub fn line_span(&self, line: usize) -> Span {
        assert!(line < self.file.lines.len());
        Span {
            low: self.file.lines[line],
            high: *self
                .file
                .lines
                .get(line + 1)
                .unwrap_or(&self.file_span().high),
        }
    }

    /// Gets the source text of a line.
    ///
    /// The string returned does not include the terminating \r or \n characters.
    ///
    /// # Panics
    ///
    ///  * If the line number is out of range
    pub fn source_line(&self, line: usize) -> &str {
        self.source_slice(self.line_span(line))
            .trim_end_matches(&['\n', '\r'][..])
    }

    /// Gets the number of lines in the file
    pub fn num_lines(&self) -> usize {
        self.file.lines.len()
    }
}

/// A line and column.
#[derive(Copy, Clone, Dupe, Hash, Eq, PartialEq, Debug)]
pub struct LineCol {
    /// The line number within the file (0-indexed).
    pub line: usize,

    /// The column within the line (0-indexed).
    pub column: usize,
}

/// A file, and a line and column range within it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SpanLoc {
    pub file: CodeMap,
    pub begin: LineCol,
    pub end: LineCol,
}

impl fmt::Display for SpanLoc {
    /// Formats the span as `filename:start_line:start_column: end_line:end_column`,
    /// or if the span is zero-length, `filename:line:column`, with a 1-indexed line and column.
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.begin == self.end {
            write!(
                f,
                "{}:{}:{}",
                self.file.name(),
                self.begin.line + 1,
                self.begin.column + 1
            )
        } else {
            write!(
                f,
                "{}:{}:{}: {}:{}",
                self.file.name(),
                self.begin.line + 1,
                self.begin.column + 1,
                self.end.line + 1,
                self.end.column + 1
            )
        }
    }
}

#[derive(Copy, Dupe, Clone, Hash, Eq, PartialEq, Debug)]
pub struct LineCol1 {
    /// The line number within the file (1-indexed).
    pub line: usize,

    /// The column within the line (1-indexed).
    pub column: usize,
}

#[doc(hidden)] // Eventually we want CodeMap to gain these features, so this will go away
#[derive(Debug, Dupe, Clone, Copy)]
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

#[test]
fn test_codemap() {
    let source = "abcd\nefghij\nqwerty";
    let codemap = CodeMap::new("test1.rs".to_owned(), source.to_owned());
    let start = codemap.file_span().low();

    // Test .name()
    assert_eq!(codemap.name(), "test1.rs");

    // Test .find_line_col()
    assert_eq!(codemap.find_line_col(start), LineCol { line: 0, column: 0 });
    assert_eq!(
        codemap.find_line_col(start + 4),
        LineCol { line: 0, column: 4 }
    );
    assert_eq!(
        codemap.find_line_col(start + 5),
        LineCol { line: 1, column: 0 }
    );
    assert_eq!(
        codemap.find_line_col(start + 16),
        LineCol { line: 2, column: 4 }
    );

    // Test .source() and .num_lines()
    assert_eq!(codemap.source(), source);
    assert_eq!(codemap.num_lines(), 3);

    // Test generic properties on each line
    for line in 0..3 {
        let line_str = codemap.source_line(line);
        let line_span = codemap.line_span(line);
        // The line_str omits trailing newlines
        assert_eq!(
            line_str.len() + if line < 2 { 1 } else { 0 },
            line_span.len() as usize
        );
        assert_eq!(line_str, source.lines().nth(line).unwrap());
        assert_eq!(codemap.find_line(line_span.low()), line);
        // The final character might be a newline, which is counted as the next line.
        // Not sure this is a good thing!
        let end = Pos(line_span.high().0 - 1);
        assert_eq!(codemap.find_line(end), line);
        assert_eq!(
            codemap.find_line_col(line_span.low()),
            LineCol { line, column: 0 }
        );
        assert_eq!(
            codemap.find_line_col(end),
            LineCol {
                line,
                column: line_span.len() as usize - 1
            }
        );
    }
}

#[test]
fn test_issue2() {
    let content = "a \nxyz\r\n";
    let codemap = CodeMap::new("<test>".to_owned(), content.to_owned());

    let span = codemap.file_span().subspan(2, 3);
    assert_eq!(
        codemap.look_up_span(span),
        SpanLoc {
            file: codemap.dupe(),
            begin: LineCol { line: 0, column: 2 },
            end: LineCol { line: 1, column: 0 }
        }
    );

    assert_eq!(codemap.source_line(0), "a ");
    assert_eq!(codemap.source_line(1), "xyz");
    assert_eq!(codemap.source_line(2), "");
}

#[test]
fn test_multibyte() {
    let content = "65°00′N 18°00′W 汉语\n🔬";
    let codemap = CodeMap::new("<test>".to_owned(), content.to_owned());

    assert_eq!(
        codemap.find_line_col(codemap.file_span().low() + 21),
        LineCol {
            line: 0,
            column: 15
        }
    );
    assert_eq!(
        codemap.find_line_col(codemap.file_span().low() + 28),
        LineCol {
            line: 0,
            column: 18
        }
    );
    assert_eq!(
        codemap.find_line_col(codemap.file_span().low() + 33),
        LineCol { line: 1, column: 1 }
    );
}
