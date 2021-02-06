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

use serde::{Deserialize, Serialize};
use starlark::{
    analysis::{LineColSpan, Lint},
    errors::Diagnostic,
};
use std::fmt::{self, Display};

#[derive(Debug, Deserialize, Clone, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
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

#[derive(Debug, Deserialize, Clone, Serialize)]
pub struct Message {
    pub path: String,
    pub span: Option<LineColSpan>,
    pub code: String,
    pub severity: Severity,
    pub name: String,
    pub description: String,
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

fn code() -> String {
    "STARLARK".to_owned()
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
                let span = LineColSpan::from_span(
                    file.find_line_col(span.low()),
                    file.find_line_col(span.high()),
                );
                Self {
                    path: file.name().to_owned(),
                    span: Some(span),
                    code: code(),
                    severity: Severity::Error,
                    name: "error".to_owned(),
                    description: format!("{:#}", message),
                }
            }
            _ => Self {
                path: file.to_owned(),
                span: None,
                code: code(),
                severity: Severity::Error,
                name: "error".to_owned(),
                description: format!("{:#}", x),
            },
        }
    }

    pub fn from_lint(x: Lint) -> Self {
        Self {
            path: x.location.file.name().to_owned(),
            span: Some(LineColSpan::from_span_loc(&x.location)),
            code: code(),
            severity: if x.serious {
                Severity::Warning
            } else {
                // Start with all non-serious errors disabled, and ramp up from there
                Severity::Disabled
            },
            name: x.short_name,
            description: x.problem,
        }
    }
}
