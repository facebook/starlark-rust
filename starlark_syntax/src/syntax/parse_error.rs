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

//! Parser-agnostic error type for parse failures.

use crate::codemap::CodeMap;
use crate::codemap::Span;
use crate::eval_exception::EvalException;

/// A parse error with a message and source span.
/// This is the common error type returned by any parser implementation,
/// independent of the underlying parsing strategy (LALRPOP, recursive descent, etc.).
pub(crate) enum ParseError {
    /// An error with a message and span, to be rendered as a diagnostic.
    Error { message: String, span: Span },
    /// An error that already has full diagnostic information (e.g., from
    /// user-defined error callbacks in the parser state).
    EvalException(EvalException),
}

impl ParseError {
    /// Convert this parse error into a `crate::Error` with source location.
    pub(crate) fn into_crate_error(self, codemap: &CodeMap) -> crate::Error {
        match self {
            ParseError::Error { message, span } => crate::Error::new_spanned(
                crate::ErrorKind::Parser(anyhow::anyhow!(message)),
                span,
                codemap,
            ),
            ParseError::EvalException(e) => e.into_error(),
        }
    }
}
