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

use crate::codemap::{CodeMap, FileSpan, Span};
use gazebo::variants::VariantName;
use std::fmt::{self, Display};

pub(crate) trait LintWarning: Display + VariantName {
    fn is_serious(&self) -> bool;
}

/// A private version of lint without the inner trait erased, useful so we can test
/// using full matching, but then erase the internal details when exporting to users.
pub(crate) struct LintT<T> {
    pub location: FileSpan,
    pub original: String,
    pub problem: T,
}

/// A lint produced by [`AstModule::lint`](crate::syntax::AstModule::lint).
#[derive(Debug)]
pub struct Lint {
    /// Which code location does this lint refer to.
    pub location: FileSpan,
    /// kebab-case constant describing this issue, e.g. `missing-return`.
    pub short_name: String,
    /// Is this code highly-likely to be wrong, rather
    /// than merely stylistically non-ideal.
    pub serious: bool,
    /// A description of the underlying problem.
    pub problem: String,
    /// The source code at [`location`](Lint::location).
    pub original: String,
}

impl Display for Lint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.problem)
    }
}

impl<T: Display> Display for LintT<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.problem)
    }
}

impl<T: LintWarning> LintT<T> {
    pub(crate) fn new(codemap: &CodeMap, span: Span, problem: T) -> Self {
        let location = codemap.file_span(span);
        Self {
            original: location.file.source_span(span).to_owned(),
            location,
            problem,
        }
    }

    pub(crate) fn erase(self) -> Lint {
        Lint {
            location: self.location,
            short_name: kebab(self.problem.variant_name()),
            serious: self.problem.is_serious(),
            problem: self.problem.to_string(),
            original: self.original,
        }
    }
}

fn kebab(xs: &str) -> String {
    let mut res = String::new();
    for x in xs.chars() {
        if x.is_uppercase() {
            if !res.is_empty() {
                res.push('-');
            }
            for y in x.to_lowercase() {
                res.push(y);
            }
        } else {
            res.push(x);
        }
    }
    res
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lint_kebab() {
        assert_eq!(kebab("Unreachable"), "unreachable");
        assert_eq!(kebab("UsingIgnored"), "using-ignored");
        assert_eq!(
            kebab("MissingReturnExpression"),
            "missing-return-expression"
        );
        assert_eq!(
            kebab("DuplicateTopLevelAssign"),
            "duplicate-top-level-assign"
        );
    }
}
