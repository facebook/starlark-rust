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

//! Error types used by Starlark, mostly [`Diagnostic`].

pub use crate::analysis::Lint;
use crate::codemap::{CodeMap, FileSpan, Span};
use annotate_snippets::{
    display_list::{DisplayList, FormatOptions},
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};
use std::{
    error::Error,
    fmt::{self, Display, Formatter},
};

pub(crate) mod did_you_mean;

/// An error plus its origination location and call stack.
///
/// The underlying [`message`](Diagnostic::message) is an [`anyhow::Error`].
/// The [`Diagnostic`] structure itself usually stored within an [`anyhow::Error`].
#[derive(Debug)]
pub struct Diagnostic {
    /// Underlying error for the [`Diagnostic`].
    /// Should _never_ be of type [`Diagnostic`] itself.
    pub message: anyhow::Error,

    /// Location where the error originated.
    pub span: Option<FileSpan>,

    /// Call stack of what called what. Most recent frames are at the end.
    pub call_stack: Vec<Frame>,
}

/// A frame of the call-stack.
#[derive(Debug)]
pub struct Frame {
    /// The name of the entry on the call-stack.
    pub name: String,
    /// The location of the definition, or [`None`] for native Rust functions.
    pub location: Option<FileSpan>,
}

impl Display for Frame {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)?;
        if let Some(loc) = &self.location {
            write!(f, " (called from {})", loc)?;
        }
        Ok(())
    }
}

impl Error for Diagnostic {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&*self.message)
    }

    fn backtrace(&self) -> Option<&std::backtrace::Backtrace> {
        Some(self.message.backtrace())
    }
}

impl Diagnostic {
    /// Create a new [`Diagnostic`] containing an underlying error and span.
    /// If the given `message` is already a [`Diagnostic`] with a [`Span`],
    /// the new span will be ignored and the original `message` returned.
    pub fn new(message: impl Into<anyhow::Error>, span: Span, codemap: CodeMap) -> anyhow::Error {
        Self::modify(message.into(), |d| d.set_span(span, codemap))
    }

    /// Modify an error by attaching diagnostic information to it - e.g. `span`/`call_stack`.
    /// If given an [`anyhow::Error`] which is a [`Diagnostic`], it will add the information to the
    /// existing [`Diagnostic`]. If not, it will wrap the error in [`Diagnostic`].
    pub fn modify(mut err: anyhow::Error, f: impl FnOnce(&mut Diagnostic)) -> anyhow::Error {
        match err.downcast_mut::<Diagnostic>() {
            Some(diag) => {
                f(diag);
                err
            }
            _ => {
                let mut err = Self {
                    message: err,
                    span: None,
                    call_stack: Vec::new(),
                };
                f(&mut err);
                err.into()
            }
        }
    }

    /// Set the [`Diagnostic::span`] field, unless it's already been set.
    pub fn set_span(&mut self, span: Span, codemap: CodeMap) {
        if self.span.is_none() {
            // We want the best span, which is likely the first person to set it
            self.span = Some(codemap.file_span(span));
        }
    }

    /// Set the [`Diagnostic::call_stack`] field, unless it's already been set.
    pub fn set_call_stack(&mut self, call_stack: impl FnOnce() -> Vec<Frame>) {
        if self.call_stack.is_empty() {
            // We want the best call stack, which is likely the first person to set it
            self.call_stack = call_stack();
        }
    }

    /// Print an error to the stderr stream. If the error is a [`Diagnostic`] it will use
    /// color-codes when printing.
    ///
    /// Note that this function doesn't print any context information if the error is a
    /// [`Diagnostic`], so you might prefer to use `eprintln!("{:#}"), err)`
    /// if you suspect there is useful context (although you won't get pretty colors).
    pub fn eprint(err: &anyhow::Error) {
        match err.downcast_ref::<Diagnostic>() {
            None => eprintln!("{:#}", err),
            Some(diag) => diagnostic_stderr(diag),
        }
    }
}

impl Display for Diagnostic {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        diagnostic_display(self, f)
    }
}

struct CallStackFmt<'a>(&'a Vec<Frame>);

impl Display for CallStackFmt<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for x in self.0.iter() {
            writeln!(f, "* {}", x)?;
        }
        Ok(())
    }
}

/////////////////////////////////////////////////////////////////////
// DISPLAY RELATED UTILITIES
// Since formatting these types is difficult, we reuse the Rust compiler
// variants by doing a conversion using annotate-snippets
// (https://github.com/rust-lang/annotate-snippets-rs)

fn get_display_list_for_diagnostic<'a>(
    annotation_label: &'a str,
    x: &'a Diagnostic,
    color: bool,
) -> DisplayList<'a> {
    fn convert_span_to_range_relative_to_first_line(
        diagnostic_span: Span,
        start_column: usize,
    ) -> (usize, usize) {
        let span_length = diagnostic_span.len() as usize;
        (start_column, start_column + span_length)
    }

    fn convert_span_to_slice<'a>(span: &'a FileSpan) -> Slice<'a> {
        let region = span.resolve_span();

        // we want the source_span to capture any whitespace ahead of the diagnostic span to
        // get the column numbers correct in the DisplayList, and any trailing source code
        // on the last line for context.
        let first_line_span = span.file.line_span(region.begin_line);
        let last_line_span = span.file.line_span(region.end_line);
        let source_span = span.span.merge(first_line_span).merge(last_line_span);

        Slice {
            source: span.file.source_span(source_span),
            line_start: 1 + region.begin_line,
            origin: Some(span.file.filename()),
            fold: false,
            annotations: vec![SourceAnnotation {
                label: "",
                annotation_type: AnnotationType::Error,
                range: convert_span_to_range_relative_to_first_line(span.span, region.begin_column),
            }],
        }
    }

    let slice = x.span.as_ref().map(convert_span_to_slice);

    let snippet = Snippet {
        title: Some(Annotation {
            label: Some(annotation_label),
            id: None,
            annotation_type: AnnotationType::Error,
        }),
        footer: Vec::new(),
        slices: slice.map(|s| vec![s]).unwrap_or_default(),
        opt: FormatOptions {
            color,
            ..Default::default()
        },
    };

    DisplayList::from(snippet)
}

fn diagnostic_display(diagnostic: &Diagnostic, f: &mut Formatter<'_>) -> fmt::Result {
    CallStackFmt(&diagnostic.call_stack).fmt(f)?;
    let annotation_label = format!("{:#}", diagnostic.message);
    // I set color to false here to make the comparison easier with tests (coloring
    // adds in pretty strange unicode chars).
    let display_list = get_display_list_for_diagnostic(&annotation_label, diagnostic, false);
    writeln!(f, "{}", display_list)
}

fn diagnostic_stderr(diagnostic: &Diagnostic) {
    eprint!("{}", CallStackFmt(&diagnostic.call_stack));
    let annotation_label = format!("{:#}", diagnostic.message);
    let display_list = get_display_list_for_diagnostic(&annotation_label, diagnostic, true);
    eprintln!("{}", display_list);
}
