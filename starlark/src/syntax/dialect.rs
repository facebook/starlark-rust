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

use crate::{errors::Diagnostic, syntax::ast::Visibility};
use codemap::{CodeMap, Span, Spanned};
use gazebo::prelude::*;
use std::sync::Arc;
use thiserror::Error;

#[derive(Error, Debug)]
enum DialectError {
    #[error("`def` is not allowed in this dialect")]
    Def,
    #[error("`lambda` is not allowed in this dialect")]
    Lambda,
    #[error("`load` is not allowed in this dialect")]
    Load,
    #[error("* keyword-only-arguments is not allowed in this dialect")]
    KeywordOnlyArguments,
    #[error("type annotations are not allowed in this dialect")]
    Types,
}

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
    /// Are `for`, `if` and other statements allowed at the top-level
    pub enable_top_level_stmt: bool,
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
        enable_top_level_stmt: false,
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
        enable_top_level_stmt: false,
    };

    /// Starlark plus `lambda`, nested `def` and other features.
    pub const Extended: Self = Self {
        enable_def: true,
        enable_lambda: true,
        enable_load: true,
        enable_keyword_only_arguments: true,
        enable_types: true,
        enable_tabs: true,
        enable_load_reexport: true,
        enable_top_level_stmt: true,
    };
}

fn err<T>(codemap: &Arc<CodeMap>, span: Span, err: DialectError) -> anyhow::Result<T> {
    Err(Diagnostic::add_span(err, span, codemap.dupe()))
}

impl Dialect {
    pub(crate) fn check_lambda<T>(
        &self,
        codemap: &Arc<CodeMap>,
        x: Spanned<T>,
    ) -> anyhow::Result<Spanned<T>> {
        if self.enable_lambda {
            Ok(x)
        } else {
            err(codemap, x.span, DialectError::Lambda)
        }
    }

    pub(crate) fn check_def<T>(
        &self,
        codemap: &Arc<CodeMap>,
        x: Spanned<T>,
    ) -> anyhow::Result<Spanned<T>> {
        if self.enable_def {
            Ok(x)
        } else {
            err(codemap, x.span, DialectError::Def)
        }
    }

    pub(crate) fn check_load<T>(
        &self,
        codemap: &Arc<CodeMap>,
        x: Spanned<T>,
    ) -> anyhow::Result<Spanned<T>> {
        if self.enable_load {
            Ok(x)
        } else {
            err(codemap, x.span, DialectError::Load)
        }
    }

    pub(crate) fn check_keyword_only_arguments<T>(
        &self,
        codemap: &Arc<CodeMap>,
        span: Span,
        x: T,
    ) -> anyhow::Result<T> {
        if self.enable_keyword_only_arguments {
            Ok(x)
        } else {
            err(codemap, span, DialectError::KeywordOnlyArguments)
        }
    }

    pub(crate) fn check_type<T>(
        &self,
        codemap: &Arc<CodeMap>,
        x: Spanned<T>,
    ) -> anyhow::Result<Spanned<T>> {
        if self.enable_types {
            Ok(x)
        } else {
            err(codemap, x.span, DialectError::Types)
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
