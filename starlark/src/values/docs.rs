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
use serde::{Deserialize, Serialize};

/// The documentation provided by a user for a specific module, object, function, etc.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DocString {
    /// The first line of a doc string. This has whitespace trimmed from it.
    pub summary: String,
    /// The contents of a doc string that follow the summary, and a single blank line.
    /// This also has whitespace trimmed from it, and it is dedented.
    pub details: Option<String>,
}

impl DocString {
    /// Parse out a docstring from a user provided string, handling dedenting, trimming, etc.
    pub fn from_docstring(user_docstring: &str) -> Option<DocString> {
        let trimmed_docs = user_docstring.trim();
        if trimmed_docs.is_empty() {
            None
        } else {
            match trimmed_docs.split1_opt("\n\n") {
                Some((summary, details)) if !summary.is_empty() && !details.is_empty() => {
                    // Dedent the details separately so that people can have the summary on the
                    // same line as the opening quotes, and the details indented on subsequent
                    // lines.
                    Some(DocString {
                        summary: summary.to_owned(),
                        details: Some(textwrap::dedent(details).trim().to_owned()),
                    })
                }
                _ => Some(DocString {
                    summary: trimmed_docs.to_owned(),
                    details: None,
                }),
            }
        }
    }
}

/// Line / column for where in a file a symbol is.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Pos {
    pub line: usize,
    pub column: usize,
}

/// The file a symbol resides in, and if available its location within that file.
///
/// `path` should be a string that can be passed into `load()` statements.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Location {
    pub path: String,
    pub position: Option<Pos>,
}

/// The main identifier for a symbol.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Identifier {
    /// The name of the symbol (e.g. the function name, a name or path for a module, etc).
    pub name: String,
    /// Where the symbol is located, or absent if it is a built-in symbol.
    pub location: Option<Location>,
}

/// The type of a given parameter, field, etc.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Type {
    /// The type string that one would find in a starlark expression.
    pub raw_type: String,
}

/// Documents a full module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Module {
    /// In general, this should be the first statement of a loaded file, if that statement is
    /// a string literal.
    pub docs: Option<DocString>,
}

/// Documents a single function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Function {
    /// Documentation for the function. If parsed, this should generally be the first statement
    /// of a function's body if that statement is a string literal. Any sections like "Args:",
    /// "Returns", etc are kept intact. It is up to the consumer to remove these sections if
    /// they are present.
    pub docs: Option<DocString>,
    /// The parameters that this function takes. Docs for these parameters should generally be
    /// extracted from the main docstring's details.
    pub params: Vec<Param>,
    /// Details about what this function returns.
    pub ret: Return,
}

/// A single parameter of a function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Param {
    /// A regular parameter that may or may not have a default value.
    Arg {
        name: String,
        docs: Option<DocString>,
        #[serde(rename = "type")]
        typ: Option<Type>,
        /// If present, this parameter has a default value. This is the `repr()` of that value.
        default_value: Option<String>,
    },
    /// Represents the "*" argument.
    NoArgs,
    /// Represents the "*args" style of argument.
    Args {
        name: String,
        docs: Option<DocString>,
        #[serde(rename = "type")]
        typ: Option<Type>,
    },
    /// Represents the "**kwargs" style of argument.
    Kwargs {
        name: String,
        docs: Option<DocString>,
        #[serde(rename = "type")]
        typ: Option<Type>,
    },
}

/// Details about the return value of a function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Return {
    /// Extra semantic details around the returned value's meaning.
    pub docs: Option<DocString>,
    #[serde(rename = "type")]
    pub typ: Option<Type>,
}

/// A single property of an object. These are explicitly not functions (see [`Member`]).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Property {
    pub docs: Option<DocString>,
    #[serde(rename = "type")]
    pub typ: Option<Type>,
}

/// A named member of an object.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Member {
    Property(Property),
    Function(Function),
}

/// An object with named functions/properties.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Object {
    pub docs: Option<DocString>,
    /// Name and details of each member of this object.
    pub members: Vec<(String, Member)>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DocItem {
    Module(Module),
    Object(Object),
    Function(Function),
}

/// The main structure that represents the documentation for a given symbol / module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Doc {
    pub id: Identifier,
    pub item: DocItem,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parses_docstring() {
        assert_eq!(DocString::from_docstring(" "), None);
        assert_eq!(
            DocString::from_docstring(" \n\nThis should be the summary\n\n"),
            Some(DocString {
                summary: "This should be the summary".to_owned(),
                details: None,
            })
        );
        assert_eq!(
            DocString::from_docstring(" \n\nThis should be the summary\n\n "),
            Some(DocString {
                summary: "This should be the summary".to_owned(),
                details: None,
            })
        );
        assert_eq!(
            DocString::from_docstring(
                r#"
        This is the summary

        This should be a multiline set of details.
        It should be:
            - Dedented
            - Trimmed
            - Split properly from the summary

"#
            ),
            Some(DocString {
                summary: "This is the summary".to_owned(),
                details: Some(
                    concat!(
                        "This should be a multiline set of details.\n",
                        "It should be:\n",
                        "    - Dedented\n",
                        "    - Trimmed\n",
                        "    - Split properly from the summary"
                    )
                    .to_owned()
                ),
            })
        );
        assert_eq!(
            DocString::from_docstring(
                r#"This is a summary line that is not dedented like the 'details'

        Typing the first line right after the """ in python docstrings is common,
        while putting the rest of the docstring indented. Just support both so it
        doesn't surprise anyone.
        "#
            ),
            Some(DocString {
                summary: "This is a summary line that is not dedented like the 'details'"
                    .to_owned(),
                details: Some(
                    concat!(
                "Typing the first line right after the \"\"\" in python docstrings is common,\n",
                "while putting the rest of the docstring indented. Just support both so it\n",
                "doesn't surprise anyone."
                )
                    .to_owned()
                ),
            })
        );
    }
}
