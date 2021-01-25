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

use crate::syntax::{ast::Visibility, lexer::LexerError};
use codemap::{Span, Spanned};

/// Starlark language dialect.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Dialect {
    /// Are `def` statements permitted
    pub enable_def: bool,
    /// Are `lambda` expressions permitted
    pub enable_lambda: bool,
    /// Are `load` statements permitted
    pub enable_load: bool,
    /// Are `*` keyword-only arguments allowed (https://www.python.org/dev/peps/pep-3102/)
    pub enable_keyword_only_arguments: bool,
    /// Are expressions allowed in type positions (https://www.python.org/dev/peps/pep-0484/)
    pub enable_types: bool,
    /// Are tabs permitted for indentation. If permitted, tabs are equivalent to 8 spaces.
    pub enable_tabs: bool,
    /// Do load() statements reexport their definition
    pub enable_load_reexport: bool,
}

// These are morally enumerations, so give them enumeration-like names
// even though they are actually global constants
#[allow(non_upper_case_globals)]
impl Dialect {
    /// Build file dialect which is used to interpret BUILD files - lacks `def`.
    pub const Simple: Self = Self {
        enable_def: false,
        enable_lambda: true,
        enable_load: true,
        enable_keyword_only_arguments: false,
        enable_types: false,
        enable_tabs: true,
        enable_load_reexport: false,
    };

    /// The Starlark language as specified in https://github.com/bazelbuild/starlark/blob/master/spec.md
    pub const Standard: Self = Self {
        enable_def: true,
        enable_lambda: false,
        enable_load: true,
        enable_keyword_only_arguments: false,
        enable_types: false,
        enable_tabs: true,
        enable_load_reexport: true, // But they plan to change it
    };

    /// Starlark plus `lambda`, nested `def` and other features.
    pub const Extended: Self = Self {
        enable_def: true,
        enable_lambda: true,
        enable_load: true,
        enable_keyword_only_arguments: true,
        enable_types: false,
        enable_tabs: true,
        enable_load_reexport: true,
    };
}

impl Dialect {
    pub(crate) fn check_lambda<T>(
        &self,
        x: Box<Spanned<T>>,
    ) -> Result<Box<Spanned<T>>, LexerError> {
        if self.enable_lambda {
            Ok(x)
        } else {
            Err(LexerError::WrappedError {
                span: x.span,
                message: "lambda is not allowed in this dialect",
            })
        }
    }

    pub(crate) fn check_def<T>(&self, x: Box<Spanned<T>>) -> Result<Box<Spanned<T>>, LexerError> {
        if self.enable_def {
            Ok(x)
        } else {
            Err(LexerError::WrappedError {
                span: x.span,
                message: "def is not allowed in this dialect",
            })
        }
    }

    pub(crate) fn check_load<T>(&self, x: Box<Spanned<T>>) -> Result<Box<Spanned<T>>, LexerError> {
        if self.enable_load {
            Ok(x)
        } else {
            Err(LexerError::WrappedError {
                span: x.span,
                message: "load is not allowed in this dialect",
            })
        }
    }

    pub(crate) fn check_keyword_only_arguments<T>(
        &self,
        span: Span,
        x: T,
    ) -> Result<T, LexerError> {
        if self.enable_keyword_only_arguments {
            Ok(x)
        } else {
            Err(LexerError::WrappedError {
                span,
                message: "* keyword-only-arguments is not allowed in this dialect",
            })
        }
    }

    pub(crate) fn check_type<T>(&self, x: Box<Spanned<T>>) -> Result<Box<Spanned<T>>, LexerError> {
        if self.enable_types {
            Ok(x)
        } else {
            Err(LexerError::WrappedError {
                span: x.span,
                message: "type annotations are not allowed in this dialect",
            })
        }
    }

    pub(crate) fn load_visibility(&self) -> Visibility {
        if self.enable_load_reexport {
            Visibility::Public
        } else {
            Visibility::Private
        }
    }
}
