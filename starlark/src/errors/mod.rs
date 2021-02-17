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

use annotate_snippets::{
    display_list::{DisplayList, FormatOptions},
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};
use anyhow::anyhow;
use codemap::{CodeMap, Span, SpanLoc};
use std::{
    error::Error,
    fmt::{self, Display, Formatter},
    sync::Arc,
};

/// An error from Starlark, complete with locations, error codes, message etc
#[derive(Debug)]
pub struct Diagnostic {
    /// Message used as the headline of the error
    /// Must be in an Arc, so we can clone it.
    pub message: anyhow::Error,

    /// Location to underline in the code
    // We'd love to make this a SpanLoc, but then we can't use the codemap_diagnostics
    // printing, as there's no way to reverse the transformation
    pub span: Option<(Span, Arc<CodeMap>)>,

    /// Call stack of what called what. Newest frames are at the end.
    pub call_stack: Vec<Frame>,
}

#[derive(Debug)]
pub struct Frame {
    pub name: String,
    pub location: Option<SpanLoc>,
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
    pub fn new(msg: impl Into<String>) -> Self {
        Self::anyhow(anyhow!(msg.into()))
    }

    pub fn anyhow(msg: impl Into<anyhow::Error>) -> Self {
        Self {
            message: msg.into(),
            span: None,
            call_stack: Vec::new(),
        }
    }

    pub fn set_span(&mut self, span: Span, codemap: Arc<CodeMap>) {
        if self.span.is_none() {
            // We want the best span, which is likely the first person to set it
            self.span = Some((span, codemap));
        }
    }

    pub fn set_call_stack(&mut self, call_stack: impl FnOnce() -> Vec<Frame>) {
        if self.call_stack.is_empty() {
            // We want the best call stack, which is likely the first person to set it
            self.call_stack = call_stack();
        }
    }

    pub fn emit_stderr(&self) {
        diagnostic_stderr(self);
    }
}

pub fn eprint_error(diagnostic: &anyhow::Error) {
    match diagnostic.downcast_ref::<Diagnostic>() {
        None => eprint!("{:#}", diagnostic),
        Some(diag) => diag.emit_stderr(),
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

    fn convert_span_to_slice<'a>(diagnostic_span: Span, codemap: &'a CodeMap) -> Slice<'a> {
        let file = codemap.find_file(diagnostic_span.low());
        let first_line_col = file.find_line_col(diagnostic_span.low());
        let last_line_col = file.find_line_col(diagnostic_span.high());

        // we want the source_span to capture any whitespace ahead of the diagnostic span to
        // get the column numbers correct in the DisplayList, and any trailing source code
        // on the last line for context.
        let first_line_span = file.line_span(first_line_col.line);
        let last_line_span = file.line_span(last_line_col.line);
        let source_span = diagnostic_span.merge(first_line_span).merge(last_line_span);

        Slice {
            source: file.source_slice(source_span),
            line_start: 1 + first_line_col.line,
            origin: Some(file.name()),
            fold: false,
            annotations: vec![SourceAnnotation {
                label: "",
                annotation_type: AnnotationType::Error,
                range: convert_span_to_range_relative_to_first_line(
                    diagnostic_span,
                    first_line_col.column,
                ),
            }],
        }
    }

    let slice = x.span.as_ref().map(|s| convert_span_to_slice(s.0, &s.1));

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
