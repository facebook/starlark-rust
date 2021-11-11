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

use std::collections::HashMap;

use gazebo::prelude::*;
use itertools::Itertools;
use once_cell::sync::Lazy;
use regex::{Regex, RegexBuilder};
use serde::{Deserialize, Serialize};

use crate as starlark;
use crate::{
    codemap::Spanned,
    syntax::ast::{AstLiteral, AstPayload, AstStmtP, ExprP, StmtP},
    values::Trace,
};

/// The documentation provided by a user for a specific module, object, function, etc.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Trace)]
pub struct DocString {
    /// The first line of a doc string. This has whitespace trimmed from it.
    pub summary: String,
    /// The contents of a doc string that follow the summary, and a single blank line.
    /// This also has whitespace trimmed from it, and it is dedented.
    pub details: Option<String>,
}

/// Controls the formatting to use when parsing `DocString`s from raw docstrings
#[derive(Copy, Clone, Dupe)]
pub enum DocStringKind {
    /// Docstrings provided by users in starlark files, following python-y documentation style.
    ///
    /// For functions, they are the piece in `"""` that come right after the `def foo():` line,
    /// and they have sections for additional details. An example from a starlark file might be:
    ///
    /// ```starlark
    /// """ Module level docs here """
    ///
    /// def some_function(val: "string") -> "string":
    ///     """ This function takes a string and returns it.
    ///
    ///     This is where an explanation might go, but I have none
    ///
    ///     Args:
    ///         val: This is the value that gets returned
    ///
    ///     Returns:
    ///         The original value, because identity functions are fun.
    /// ```
    Starlark,
    /// Docstrings used with `#[starlark_module]` in rust.
    ///
    /// These are the documentation strings prefixed by `///` (like these docs) on
    /// `#[starlark_module]`, and the functions / attributes within it. It supports
    /// a section `# Arguments`, and `# Returns`, and removes some lines from code
    /// blocks that are valid for rustdoc, but not useful for people using these
    /// functions via starlark. An example might be something like:
    ///
    /// ```ignore
    /// /// These are where the module / object level docs go
    /// #[starlark_module]
    /// fn add_some_value(builder: &mut GlobalsBuilder) {
    ///     /// attr1 is an attribute that does nothing interesting.
    ///     #[attribute]
    ///     fn attr1(_this: Value<'v>) -> String {
    ///         Ok("attr1".to_owned())
    ///     }
    ///     /// Copies a string
    ///     ///
    ///     /// This is where details would be, if this were
    ///     /// a more interesting function.
    ///     ///
    ///     /// # Arguments
    ///     /// * `s`: This is string that is returned.
    ///     ///
    ///     /// # Returns
    ///     /// The a copy of the original string.
    ///     fn copy_string(s: &str) -> String {
    ///         Ok(s.to_owned())
    ///     }
    /// }
    /// ```
    Rust,
}

impl DocString {
    /// Extracts the docstring from a function or module body, iff the first
    /// statement is a string literal.
    pub fn extract_raw_starlark_docstring<P: AstPayload>(body: &AstStmtP<P>) -> Option<String> {
        if let StmtP::Statements(stmts) = &body.node {
            if let Some(Spanned {
                node:
                    StmtP::Expression(Spanned {
                        node: ExprP::Literal(AstLiteral::String(s)),
                        ..
                    }),
                ..
            }) = stmts.first()
            {
                return Some(s.node.to_owned());
            }
        };
        None
    }

    /// Do common work to parse a docstring (dedenting, splitting summary and details, etc)
    pub fn from_docstring(kind: DocStringKind, user_docstring: &str) -> Option<DocString> {
        let trimmed_docs = user_docstring.trim();
        if trimmed_docs.is_empty() {
            None
        } else {
            static SPLIT_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\n[ ]*\n").unwrap());
            let split: Option<(&str, &str)> = SPLIT_RE.splitn(trimmed_docs, 2).collect_tuple();
            let (summary, details) = match split {
                Some((summary, details)) if !summary.is_empty() && !details.is_empty() => {
                    // Dedent the details separately so that people can have the summary on the
                    // same line as the opening quotes, and the details indented on subsequent
                    // lines.
                    let details = match kind {
                        DocStringKind::Starlark => textwrap::dedent(details).trim().to_owned(),
                        DocStringKind::Rust => {
                            Self::remove_rust_comments(textwrap::dedent(details).trim())
                        }
                    };
                    (summary, Some(details))
                }
                _ => (trimmed_docs, None),
            };

            // Remove any newlines (and surrounding whitespace) in the summary, and
            // replace them with a single space.
            static NEWLINES_RE: Lazy<Regex> =
                Lazy::new(|| Regex::new(r"(\S)\s*\n\s*(\S)").unwrap());
            let summary = NEWLINES_RE.replace_all(summary, r"$1 $2").to_string();

            Some(DocString { summary, details })
        }
    }

    /// Removes rustdoc-style commented out lines from code blocks.
    fn remove_rust_comments(details: &str) -> String {
        static CODEBLOCK_RE: Lazy<Regex> = Lazy::new(|| {
            RegexBuilder::new(r"```(\w*)\n.*?```")
                .dot_matches_new_line(true)
                .build()
                .expect("regex to compile")
        });
        static COMMENT_RE: Lazy<Regex> = Lazy::new(|| {
            RegexBuilder::new(r"^# .*$\n")
                .multi_line(true)
                .build()
                .expect("regex to compile")
        });
        CODEBLOCK_RE
            .replace_all(details, |caps: &regex::Captures| {
                match caps.get(1).expect("language group").as_str() {
                    "" | "rust" => COMMENT_RE
                        .replace_all(caps.get(0).expect("$0 to exist").as_str(), "")
                        .to_string(),
                    _ => caps.get(0).expect("$0 to exist").as_str().to_owned(),
                }
            })
            .to_string()
    }

    /// Join lines up, dedent them, and trim them
    fn join_and_dedent_lines(lines: &[String]) -> String {
        textwrap::dedent(&lines.join("\n")).trim().to_owned()
    }

    /// Parse out parameter docs from an "Args:" section of a docstring
    ///
    /// `args_section` should be dedented, and generally should just be the `args` key of
    /// the `DocString::parse_params()` function call. This is done as a separate function
    /// to reduce the number of times that sections are parsed out of docstring (e.g. if
    /// a user wants both the `Args:` and `Returns:` sections)
    pub fn parse_params(args_section: &str) -> HashMap<String, String> {
        static ARG_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"^(\*{0,2}\w+):\s*(.*)").unwrap());
        static INDENTED_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"^(?:\s|$)").unwrap());

        let mut ret = HashMap::new();
        let mut current_arg = None;
        let mut current_text = vec![];

        for line in args_section.lines() {
            if let Some(matches) = ARG_RE.captures(line) {
                if let Some(a) = current_arg.take() {
                    ret.insert(a, Self::join_and_dedent_lines(&current_text));
                }

                current_arg = Some(matches.get(1).unwrap().as_str().to_owned());

                let doc_match = matches.get(2).unwrap();
                current_text = vec![format!(
                    "{}{}",
                    " ".repeat(doc_match.start()),
                    doc_match.as_str()
                )];
            } else if current_arg.is_some() && INDENTED_RE.is_match(line) {
                current_text.push(line.to_owned());
            }
        }

        if let Some(a) = current_arg.take() {
            ret.insert(a, Self::join_and_dedent_lines(&current_text));
        }

        ret
    }

    /// Parse the various sections out of a doc string.
    ///
    /// "sections" are the various things in doc strings like "Arguments:", "Returns:", etc
    ///
    /// A string like:
    ///
    /// """
    /// Some summary
    ///
    /// Details about the function go here
    ///     Arguments:
    ///         arg_foo: The foo for you
    /// """
    ///
    /// would return a mapping of `{"arguments": "arg_foo: The foo for you"}`
    pub fn parse_sections(&self) -> HashMap<String, String> {
        let mut ret = HashMap::new();

        if let Some(details) = &self.details {
            static SECTION_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"^([\w -]+):\s*$").unwrap());
            static INDENTED_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"^(?:\s|$)").unwrap());

            let mut current_section = None;
            let mut current_section_text = vec![];
            for line in details.lines() {
                if let Some(matches) = SECTION_RE.captures(line) {
                    if let Some(s) = current_section.take() {
                        ret.insert(s, Self::join_and_dedent_lines(&current_section_text));
                    }
                    current_section = Some(matches.get(1).unwrap().as_str().to_ascii_lowercase());
                    current_section_text = vec![];
                } else if current_section.is_some() && INDENTED_RE.is_match(line) {
                    current_section_text.push(line.to_owned());
                }
            }

            if let Some(s) = current_section.take() {
                ret.insert(s, Self::join_and_dedent_lines(&current_section_text));
            }
        }
        ret
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
    fn parses_starlark_docstring() {
        assert_eq!(
            DocString::from_docstring(DocStringKind::Starlark, " "),
            None
        );
        assert_eq!(
            DocString::from_docstring(
                DocStringKind::Starlark,
                " \n\nThis should be the summary\n\n"
            ),
            Some(DocString {
                summary: "This should be the summary".to_owned(),
                details: None,
            })
        );
        assert_eq!(
            DocString::from_docstring(
                DocStringKind::Starlark,
                " \n\nThis should be the summary\n\n "
            ),
            Some(DocString {
                summary: "This should be the summary".to_owned(),
                details: None,
            })
        );
        assert_eq!(
            DocString::from_docstring(
                DocStringKind::Starlark,
                "Summary line here\n    \nDetails after some spaces\n\nand some more newlines"
            ),
            Some(DocString {
                summary: "Summary line here".to_owned(),
                details: Some("Details after some spaces\n\nand some more newlines".to_owned()),
            })
        );
        assert_eq!(
            DocString::from_docstring(
                DocStringKind::Starlark,
                r#"
        This is the summary.
          It has multiple lines and some spaces, and should be collapsed

        This should be a multiline set of details.
        It should be:
            - Dedented
            - Trimmed
            - Split properly from the summary

"#
            ),
            Some(DocString {
                summary: "This is the summary. It has multiple lines and some spaces, and should be collapsed".to_owned(),
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
            DocString::from_docstring(DocStringKind::Starlark,
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

    #[test]
    fn parses_rust_docstring() {
        let raw = r#"
        This is the summary line
          that sometimes is split on two lines

        This is the second part. It has some code blocks

        ```
        # foo() {
        "bar"
        # }
        ```

        ```python
        # This is a python comment. Leave it be
        print(1)
        ```

        ```rust
        # other_foo() {
        "other_bar"
        # }
        ```
        "#;

        let parsed = DocString::from_docstring(DocStringKind::Rust, raw).unwrap();
        assert_eq!(
            "This is the summary line that sometimes is split on two lines",
            parsed.summary
        );
        assert_eq!(
            concat!(
                "This is the second part. It has some code blocks\n\n",
                "```\n",
                "\"bar\"\n",
                "```\n\n",
                "```python\n",
                "# This is a python comment. Leave it be\n",
                "print(1)\n",
                "```\n\n",
                "```rust\n",
                "\"other_bar\"",
                "\n```"
            ),
            parsed.details.unwrap()
        );
    }

    #[test]
    fn parses_sections_from_docstring() {
        let docstring = r#"This is an example docstring

        We have some details up here that should not be parsed

        Some empty section:
        Example:
            First line of the section

            A newline with no space after it before the second one,
                and a third that's indented further.
        This is not in the arguments section

        Last:
            This is something in the last section
        "#;

        let mut expected = HashMap::new();
        expected.insert("some empty section".to_owned(), "".to_owned());
        expected.insert(
            "last".to_owned(),
            "This is something in the last section".to_owned(),
        );
        expected.insert(
            "example".to_owned(),
            concat!(
                "First line of the section\n\n",
                "A newline with no space after it before the second one,\n",
                "    and a third that's indented further."
            )
            .to_owned(),
        );

        let sections = DocString::from_docstring(DocStringKind::Starlark, docstring)
            .unwrap()
            .parse_sections();

        assert_eq!(sections, expected);
    }

    #[test]
    fn parses_params_from_starlark_docstring() {
        let docstring = r#"This is an example docstring

        Args:
            arg_foo: The argument named foo
            arg_bar: The argument named bar. It has
                     a longer doc string that spans
                     over three lines
            *args: Docs for args
            **kwargs: Docs for kwargs
        "#;

        let mut expected = HashMap::new();
        expected.insert("arg_foo".to_owned(), "The argument named foo".to_owned());
        expected.insert(
            "arg_bar".to_owned(),
            concat!(
                "The argument named bar. It has\n",
                "a longer doc string that spans\n",
                "over three lines"
            )
            .to_owned(),
        );
        expected.insert("*args".to_owned(), "Docs for args".to_owned());
        expected.insert("**kwargs".to_owned(), "Docs for kwargs".to_owned());

        let param_docs = DocString::from_docstring(DocStringKind::Starlark, docstring)
            .unwrap()
            .parse_sections()
            .get("args")
            .map(|s| DocString::parse_params(s))
            .unwrap();

        assert_eq!(param_docs, expected);
    }
}
