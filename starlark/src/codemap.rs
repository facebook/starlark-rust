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
use gazebo::prelude::*;
use std::{
    cmp,
    fmt::{self, Display},
    hash::Hash,
    ops::{Add, Deref, DerefMut},
    sync::Arc,
};

/// A small, `Copy`, value representing a position in a `CodeMap`'s file.
#[derive(
    Copy, Clone, Dupe, Hash, Eq, PartialEq, Ord, PartialOrd, Debug, Default
)]
pub struct Pos(u32);

impl Pos {
    pub fn new(x: u32) -> Self {
        Self(x)
    }
}

impl Add<u32> for Pos {
    type Output = Pos;
    fn add(self, other: u32) -> Pos {
        Pos(self.0 + other)
    }
}

/// A range of text within a CodeMap.
#[derive(Copy, Dupe, Clone, Hash, Eq, PartialEq, Debug, Default)]
pub struct Span {
    /// The position in the codemap representing the first byte of the span.
    begin: Pos,

    /// The position after the last byte of the span.
    end: Pos,
}

impl Span {
    /// Create a new span. Panics if `end < begin`.
    pub fn new(begin: Pos, end: Pos) -> Self {
        assert!(begin <= end);
        Span { begin, end }
    }

    /// Makes a span from offsets relative to the start of this span.
    ///
    /// Panics if `end < begin` or if `end` is beyond the length of the span.
    pub fn subspan(self, begin: u32, end: u32) -> Span {
        assert!(end >= begin);
        assert!(self.begin + end <= self.end);
        Span {
            begin: self.begin + begin,
            end: self.begin + end,
        }
    }

    /// Checks if a span is contained within this span.
    pub fn contains(self, other: Span) -> bool {
        self.begin <= other.begin && self.end >= other.end
    }

    /// The position in the codemap representing the first byte of the span.
    pub fn begin(self) -> Pos {
        self.begin
    }

    /// The position after the last byte of the span.
    pub fn end(self) -> Pos {
        self.end
    }

    /// The length in bytes of the text of the span
    pub fn len(self) -> u32 {
        self.end.0 - self.begin.0
    }

    /// Create a span that encloses both `self` and `other`.
    pub fn merge(self, other: Span) -> Span {
        Span {
            begin: cmp::min(self.begin, other.begin),
            end: cmp::max(self.end, other.end),
        }
    }
}

/// Associate a Span with a value of arbitrary type (e.g. an AST node).
#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn into_map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            span: self.span,
        }
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.node
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.node
    }
}

/// A data structure recording a source code file for position lookup.
#[derive(Clone, Dupe)]
pub struct CodeMap(Arc<CodeMapData>);

/// A `CodeMap`'s record of a source file.
pub(crate) struct CodeMapData {
    /// The filename as it would be displayed in an error message.
    filename: String,
    /// Contents of the file.
    source: String,
    /// Byte positions of line beginnings.
    lines: Vec<Pos>,
}

impl Default for CodeMap {
    fn default() -> Self {
        Self::new("".to_owned(), "".to_owned())
    }
}

impl fmt::Debug for CodeMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "CodeMap({:?})", self.0.filename)
    }
}

impl PartialEq for CodeMap {
    /// Compares by identity
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for CodeMap {}

impl CodeMap {
    /// Creates an new `CodeMap`.
    pub(crate) fn new(filename: String, source: String) -> CodeMap {
        let mut lines = vec![Pos(0)];
        lines.extend(source.match_indices('\n').map(|(p, _)| Pos(p as u32 + 1)));

        CodeMap(Arc::new(CodeMapData {
            filename,
            source,
            lines,
        }))
    }

    /// Only used internally for profiling optimisations
    pub(crate) fn get_ptr(&self) -> &Arc<CodeMapData> {
        &self.0
    }

    fn full_span(&self) -> Span {
        Span {
            begin: Pos(0),
            end: Pos(self.0.source.len() as u32),
        }
    }

    /// Gets the file and its line and column ranges represented by a `Span`.
    pub fn file_span(&self, span: Span) -> FileSpan {
        FileSpan {
            file: self.dupe(),
            span,
        }
    }

    /// Gets the name of the file
    pub fn filename(&self) -> &str {
        &self.0.filename
    }

    /// Gets the line number of a Pos.
    ///
    /// The lines are 0-indexed (first line is numbered 0)
    ///
    /// Panics if `pos` is not within this file's span.
    pub(crate) fn find_line(&self, pos: Pos) -> usize {
        assert!(pos <= self.full_span().end());
        match self.0.lines.binary_search(&pos) {
            Ok(i) => i,
            Err(i) => i - 1,
        }
    }

    /// Gets the line and column of a Pos.
    ///
    /// Panics if `pos` is not with this file's span or
    /// if `pos` points to a byte in the middle of a UTF-8 character.
    fn find_line_col(&self, pos: Pos) -> LineCol {
        let line = self.find_line(pos);
        let line_span = self.line_span(line);
        let byte_col = pos.0 - line_span.begin.0;
        let column = self.source_span(line_span)[..byte_col as usize]
            .chars()
            .count();

        LineCol { line, column }
    }

    /// Gets the full source text of the file
    pub fn source(&self) -> &str {
        &self.0.source
    }

    /// Gets the source text of a Span.
    ///
    /// Panics if `span` is not entirely within this file.
    pub fn source_span(&self, span: Span) -> &str {
        &self.0.source[(span.begin.0 as usize)..(span.end.0 as usize)]
    }

    /// Gets the span representing a line by line number.
    ///
    /// The line number is 0-indexed (first line is numbered 0). The returned span includes the
    /// line terminator.
    ///
    /// Panics if the line number is out of range.
    pub fn line_span(&self, line: usize) -> Span {
        assert!(line < self.0.lines.len());
        Span {
            begin: self.0.lines[line],
            end: *self.0.lines.get(line + 1).unwrap_or(&self.full_span().end),
        }
    }

    pub fn resolve_span(&self, span: Span) -> ResolvedSpan {
        let begin = self.find_line_col(span.begin);
        let end = self.find_line_col(span.end);
        ResolvedSpan::from_span(begin, end)
    }

    /// Gets the source text of a line.
    ///
    /// The string returned does not include the terminating \r or \n characters.
    ///
    /// Panics if the line number is out of range.
    pub fn source_line(&self, line: usize) -> &str {
        self.source_span(self.line_span(line))
            .trim_end_matches(&['\n', '\r'][..])
    }

    /// Gets the number of lines in the file
    pub fn num_lines(&self) -> usize {
        self.0.lines.len()
    }
}

/// A line and column.
#[derive(Copy, Clone, Dupe, Hash, Eq, PartialEq, Debug)]
struct LineCol {
    /// The line number within the file (0-indexed).
    pub line: usize,

    /// The column within the line (0-indexed).
    pub column: usize,
}

/// A file, and a line and column range within it.
#[derive(Clone, Dupe, Eq, PartialEq, Debug)]
pub struct FileSpan {
    pub file: CodeMap,
    pub span: Span,
}

impl fmt::Display for FileSpan {
    /// Formats the span as `filename:start_line:start_column: end_line:end_column`,
    /// or if the span is zero-length, `filename:line:column`, with a 1-indexed line and column.
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}:{}", self.file.filename(), self.resolve_span())
    }
}

impl FileSpan {
    pub fn resolve_span(&self) -> ResolvedSpan {
        self.file.resolve_span(self.span)
    }

    pub fn resolve(&self) -> ResolvedFileSpan {
        ResolvedFileSpan {
            file: self.file.filename().to_owned(),
            span: self.file.resolve_span(self.span),
        }
    }
}

/// The locations of values within a span.
/// All are 0-based, but print out with 1-based.
#[derive(Debug, Dupe, Clone, Copy, PartialEq, Eq)]
pub struct ResolvedSpan {
    pub begin_line: usize,
    pub begin_column: usize,
    pub end_line: usize,
    pub end_column: usize,
}

impl Display for ResolvedSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let single_line = self.begin_line == self.end_line;
        let is_empty = single_line && self.begin_column == self.end_column;

        if is_empty {
            write!(f, "{}:{}", self.begin_line + 1, self.begin_column + 1)
        } else if single_line {
            write!(
                f,
                "{}:{}-{}",
                self.begin_line + 1,
                self.begin_column + 1,
                self.end_column + 1
            )
        } else {
            write!(
                f,
                "{}:{}-{}:{}",
                self.begin_line + 1,
                self.begin_column + 1,
                self.end_line + 1,
                self.end_column + 1
            )
        }
    }
}

impl ResolvedSpan {
    fn from_span(begin: LineCol, end: LineCol) -> Self {
        Self {
            begin_line: begin.line,
            begin_column: begin.column,
            end_line: end.line,
            end_column: end.column,
        }
    }
}

#[derive(Debug)]
pub struct ResolvedFileSpan {
    pub file: String,
    pub span: ResolvedSpan,
}

impl Display for ResolvedFileSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.file, self.span)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_codemap() {
        let source = "abcd\nefghij\nqwerty";
        let codemap = CodeMap::new("test1.rs".to_owned(), source.to_owned());
        let start = codemap.full_span().begin();

        // Test .name()
        assert_eq!(codemap.filename(), "test1.rs");

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
            assert_eq!(codemap.find_line(line_span.begin()), line);
            // The final character might be a newline, which is counted as the next line.
            // Not sure this is a good thing!
            let end = Pos(line_span.end().0 - 1);
            assert_eq!(codemap.find_line(end), line);
            assert_eq!(
                codemap.find_line_col(line_span.begin()),
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

        let span = codemap.full_span().subspan(2, 3);
        assert_eq!(
            codemap.resolve_span(span),
            ResolvedSpan {
                begin_line: 0,
                begin_column: 2,
                end_line: 1,
                end_column: 0
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
            codemap.find_line_col(codemap.full_span().begin() + 21),
            LineCol {
                line: 0,
                column: 15
            }
        );
        assert_eq!(
            codemap.find_line_col(codemap.full_span().begin() + 28),
            LineCol {
                line: 0,
                column: 18
            }
        );
        assert_eq!(
            codemap.find_line_col(codemap.full_span().begin() + 33),
            LineCol { line: 1, column: 1 }
        );
    }

    #[test]
    fn test_line_col_span_display_point() {
        let line_col = LineCol { line: 0, column: 0 };
        let span = ResolvedSpan::from_span(line_col, line_col);
        assert_eq!(span.to_string(), "1:1");
    }

    #[test]
    fn test_line_col_span_display_single_line_span() {
        let begin = LineCol { line: 0, column: 0 };
        let end = LineCol {
            line: 0,
            column: 32,
        };
        let span = ResolvedSpan::from_span(begin, end);
        assert_eq!(span.to_string(), "1:1-33");
    }

    #[test]
    fn test_line_col_span_display_multi_line_span() {
        let begin = LineCol { line: 0, column: 0 };
        let end = LineCol {
            line: 2,
            column: 32,
        };
        let span = ResolvedSpan::from_span(begin, end);
        assert_eq!(span.to_string(), "1:1-3:33");
    }
}
