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
//! let file = codemap.get_file();
//! let string_literal_span = file.span.subspan(24, 31);
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
    hash::{Hash, Hasher},
    ops::{Add, Deref, Sub},
    sync::Arc,
};

/// A small, `Copy`, value representing a position in a `CodeMap`'s file.
#[derive(
    Copy, Clone, Dupe, Hash, Eq, PartialEq, Ord, PartialOrd, Debug, Default
)]
pub struct Pos(u32);

impl Add<u64> for Pos {
    type Output = Pos;
    fn add(self, other: u64) -> Pos {
        Pos(self.0 + other as u32)
    }
}

impl Sub<Pos> for Pos {
    type Output = u64;
    fn sub(self, other: Pos) -> u64 {
        (self.0 - other.0) as u64
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
    pub fn subspan(self, begin: u64, end: u64) -> Span {
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
    pub fn len(self) -> u64 {
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
#[derive(Debug, Clone, Dupe)]
pub struct CodeMap {
    file: Arc<File>,
}

impl Default for CodeMap {
    fn default() -> Self {
        Self::new("".to_owned(), "".to_owned())
    }
}

impl CodeMap {
    /// Creates an new `CodeMap`.
    pub fn new(filename: String, contents: String) -> CodeMap {
        let low = Pos(1);
        let high = low + contents.len() as u64;
        let mut lines = vec![low];
        lines.extend(
            contents
                .match_indices('\n')
                .map(|(p, _)| low + (p + 1) as u64),
        );

        CodeMap {
            file: Arc::new(File {
                span: Span { low, high },
                name: filename,
                source: contents,
                lines,
            }),
        }
    }

    /// Looks up a `File`
    pub fn get_file(&self) -> &Arc<File> {
        &self.file
    }

    /// Gets the file, line, and column represented by a `Pos`.
    pub fn look_up_pos(&self, pos: Pos) -> Loc {
        let file = self.get_file();
        let position = file.find_line_col(pos);
        Loc {
            file: file.dupe(),
            position,
        }
    }

    /// Gets the file and its line and column ranges represented by a `Span`.
    pub fn look_up_span(&self, span: Span) -> SpanLoc {
        let file = self.get_file();
        let begin = file.find_line_col(span.low);
        let end = file.find_line_col(span.high);
        SpanLoc {
            file: file.dupe(),
            begin,
            end,
        }
    }
}

/// A `CodeMap`'s record of a source file.
pub struct File {
    /// The span representing the entire file.
    pub span: Span,

    /// The filename as it would be displayed in an error message.
    name: String,

    /// Contents of the file.
    source: String,

    /// Byte positions of line beginnings.
    lines: Vec<Pos>,
}

impl File {
    /// Gets the name of the file
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Gets the line number of a Pos.
    ///
    /// The lines are 0-indexed (first line is numbered 0)
    ///
    /// # Panics
    ///
    ///  * If `pos` is not within this file's span
    pub fn find_line(&self, pos: Pos) -> usize {
        assert!(pos >= self.span.low);
        assert!(pos <= self.span.high);
        match self.lines.binary_search(&pos) {
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
        &self.source
    }

    /// Gets the source text of a Span.
    ///
    /// # Panics
    ///
    ///   * If `span` is not entirely within this file.
    pub fn source_slice(&self, span: Span) -> &str {
        assert!(self.span.contains(span));
        &self.source[((span.low - self.span.low) as usize)..((span.high - self.span.low) as usize)]
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
        assert!(line < self.lines.len());
        Span {
            low: self.lines[line],
            high: *self.lines.get(line + 1).unwrap_or(&self.span.high),
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
        self.lines.len()
    }
}

impl fmt::Debug for File {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "File({:?})", self.name)
    }
}

impl PartialEq for File {
    /// Compares by identity
    fn eq(&self, other: &File) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for File {}

impl Hash for File {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.span.hash(hasher);
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

/// A file, and a line and column within it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Loc {
    pub file: Arc<File>,
    pub position: LineCol,
}

impl fmt::Display for Loc {
    /// Formats the location as `filename:line:column`, with a 1-indexed
    /// line and column.
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}:{}:{}",
            self.file.name,
            self.position.line + 1,
            self.position.column + 1
        )
    }
}

/// A file, and a line and column range within it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct SpanLoc {
    pub file: Arc<File>,
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
                self.file.name,
                self.begin.line + 1,
                self.begin.column + 1
            )
        } else {
            write!(
                f,
                "{}:{}:{}: {}:{}",
                self.file.name,
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
    let codemap = CodeMap::new("test1.rs".to_owned(), "abcd\nefghij\nqwerty".to_owned());

    assert_eq!(codemap.get_file().name(), "test1.rs");
    assert_eq!(codemap.get_file().name(), "test1.rs");

    let f = codemap.get_file();
    assert_eq!(f.name, "test1.rs");
    assert_eq!(
        f.find_line_col(f.span.low()),
        LineCol { line: 0, column: 0 }
    );
    assert_eq!(
        f.find_line_col(f.span.low() + 4),
        LineCol { line: 0, column: 4 }
    );
    assert_eq!(
        f.find_line_col(f.span.low() + 5),
        LineCol { line: 1, column: 0 }
    );
    assert_eq!(
        f.find_line_col(f.span.low() + 16),
        LineCol { line: 2, column: 4 }
    );
}

#[test]
fn test_issue2() {
    let content = "a \nxyz\r\n";
    let codemap = CodeMap::new("<test>".to_owned(), content.to_owned());
    let file = codemap.get_file();

    let span = file.span.subspan(2, 3);
    assert_eq!(
        codemap.look_up_span(span),
        SpanLoc {
            file: file.dupe(),
            begin: LineCol { line: 0, column: 2 },
            end: LineCol { line: 1, column: 0 }
        }
    );

    assert_eq!(file.source_line(0), "a ");
    assert_eq!(file.source_line(1), "xyz");
    assert_eq!(file.source_line(2), "");
}

#[test]
fn test_multibyte() {
    let content = "65°00′N 18°00′W 汉语\n🔬";
    let codemap = CodeMap::new("<test>".to_owned(), content.to_owned());
    let file = codemap.get_file();

    assert_eq!(
        codemap.look_up_pos(file.span.low() + 21),
        Loc {
            file: file.dupe(),
            position: LineCol {
                line: 0,
                column: 15
            }
        }
    );
    assert_eq!(
        codemap.look_up_pos(file.span.low() + 28),
        Loc {
            file: file.dupe(),
            position: LineCol {
                line: 0,
                column: 18
            }
        }
    );
    assert_eq!(
        codemap.look_up_pos(file.span.low() + 33),
        Loc {
            file: file.dupe(),
            position: LineCol { line: 1, column: 1 }
        }
    );
}
