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

use gazebo::prelude::*;
use serde::Serialize;
use starlark::{
    analysis::{LineColSpan, Lint},
    errors::Diagnostic,
};
use std::fmt::{self, Display};

/// A standardised set of severities.
#[derive(Debug, Serialize, Dupe, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    // Not all severities are used right now
    #[allow(dead_code)]
    Advice,
    Disabled,
}

impl Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Severity::Error => "Error",
            Severity::Warning => "Warning",
            Severity::Advice => "Advice",
            Severity::Disabled => "Disabled",
        })
    }
}

#[derive(Debug, Clone)]
pub struct Message {
    pub path: String,
    pub span: Option<LineColSpan>,
    pub severity: Severity,
    pub name: String,
    pub description: String,
    /// The text referred to by span
    pub original: Option<String>,
}

impl Display for Message {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}:", self.severity, self.path)?;
        if let Some(span) = self.span {
            write!(f, "{}", span)?;
        }
        write!(f, " {}", self.description)
    }
}

impl Message {
    pub fn from_anyhow(file: &str, x: anyhow::Error) -> Self {
        match x.downcast_ref::<Diagnostic>() {
            Some(Diagnostic {
                message,
                span: Some((span, codemap)),
                ..
            }) => {
                let file = codemap.find_file(span.low());
                let original = file.source_slice(*span).to_owned();
                let span = LineColSpan::from_span(
                    file.find_line_col(span.low()),
                    file.find_line_col(span.high()),
                );
                Self {
                    path: file.name().to_owned(),
                    span: Some(span),
                    severity: Severity::Error,
                    name: "error".to_owned(),
                    description: format!("{:#}", message),
                    original: Some(original),
                }
            }
            _ => Self {
                path: file.to_owned(),
                span: None,
                severity: Severity::Error,
                name: "error".to_owned(),
                description: format!("{:#}", x),
                original: None,
            },
        }
    }

    pub fn from_lint(x: Lint) -> Self {
        Self {
            path: x.location.file.name().to_owned(),
            span: Some(LineColSpan::from_span_loc(&x.location)),
            severity: if x.serious {
                Severity::Warning
            } else {
                // Start with all non-serious errors disabled, and ramp up from there
                Severity::Disabled
            },
            name: x.short_name,
            description: x.problem,
            original: Some(x.original),
        }
    }
}

/// A JSON-deriving type that gives a stable interface to downstream types.
/// Do NOT change this type, change Message instead.
#[derive(Debug, Clone, Serialize)]
pub struct LintMessage {
    path: String,
    line: Option<usize>,
    char: Option<usize>,
    code: String,
    severity: Severity,
    name: String,
    description: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    original: Option<String>,
}

impl LintMessage {
    pub fn new(x: Message) -> Self {
        Self {
            path: x.path,
            line: x.span.map(|x| x.begin.line),
            char: x.span.map(|x| x.begin.column),
            code: "STARLARK".to_owned(),
            severity: x.severity,
            name: x.name,
            description: Some(x.description),
            original: x.original,
        }
    }
}
