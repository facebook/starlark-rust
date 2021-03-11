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

//! String interpolation-related code.
//! Based on <https://docs.python.org/3/library/stdtypes.html#printf-style-string-formatting>

use crate::values::{tuple::Tuple, Heap, Value, ValueLike};
use gazebo::prelude::*;
use std::{fmt::Write, iter};
use thiserror::Error;

const AFTER_PERCENT: &str = "'%' must be followed by an optional name and a specifier ('s', 'r', 'd', 'i', 'o', 'x', 'X', 'c') or '%'";

/// Operator `%` format or evaluation errors
#[derive(Clone, Dupe, Debug, Error)]
enum StringInterpolationError {
    #[error(
        "Unexpected EOF in format string. Could not find ')' when parsing '%(name)f' expression"
    )]
    UnexpectedEOFClosingParen,
    /// `%` must be followed by specifier.
    #[error("Unexpected EOF in format string. {}", AFTER_PERCENT)]
    UnexpectedEOFPercent,
    #[error("Unknown format string specifier '{}'. {}", .0.escape_default(), AFTER_PERCENT)]
    UnknownSpecifier(char),
    #[error("Invalid UTF-8 codepoint 0x{:x} passed for %c formatter", .0)]
    ValueNotInUTFRange(u32),
    /// Interpolation parameter is too big for the format string.
    #[error("Too many arguments for format string")]
    TooManyParameters,
    /// Interpolation parameter is too small for the format string.
    #[error("Not enough arguments for format string")]
    NotEnoughParameters,
    #[error("'%c' formatter requires a single-character string")]
    ValueNotChar,
}

/// Format char
enum ArgFormat {
    // str(x)
    Str,
    // repr(x)
    Repr,
    // signed integer decimal
    Dec,
    // signed octal
    Oct,
    // signed hexadecimal, lowercase
    HexLower,
    // signed hexadecimal, uppercase
    HexUpper,
    // x for string, chr(x) for int
    Char,
    // `%` sign
    Percent,
}

impl ArgFormat {
    fn format_arg(&self, out: &mut String, arg: Value) -> anyhow::Result<()> {
        match self {
            // Equivalent to `write!(out, "{}", arg.to_str()).unwrap()`, but avoid
            // allocating a separate `String` on the way.
            ArgFormat::Str => match arg.unpack_str() {
                None => arg.collect_repr(out),
                Some(v) => out.push_str(v),
            },
            ArgFormat::Repr => arg.collect_repr(out),
            ArgFormat::Dec => write!(out, "{}", arg.to_int()?).unwrap(),
            ArgFormat::Oct => {
                let v = arg.to_int()?;
                write!(
                    out,
                    "{}{:o}",
                    if v < 0 { "-" } else { "" },
                    v.wrapping_abs() as u64
                )
                .unwrap();
            }
            ArgFormat::HexLower => {
                let v = arg.to_int()?;
                write!(
                    out,
                    "{}{:x}",
                    if v < 0 { "-" } else { "" },
                    v.wrapping_abs() as u64
                )
                .unwrap();
            }
            ArgFormat::HexUpper => {
                let v = arg.to_int()?;
                write!(
                    out,
                    "{}{:X}",
                    if v < 0 { "-" } else { "" },
                    v.wrapping_abs() as u64
                )
                .unwrap();
            }
            ArgFormat::Char => match arg.unpack_str() {
                Some(arg) => {
                    let mut chars = arg.chars();
                    let c = chars.next();
                    match c {
                        Some(c) if chars.next().is_none() => out.push(c),
                        _ => return Err(StringInterpolationError::ValueNotChar.into()),
                    }
                }
                None => {
                    let i = arg.to_int()? as u32;
                    match std::char::from_u32(i) {
                        Some(c) => write!(out, "{}", c).unwrap(),
                        None => {
                            return Err(StringInterpolationError::ValueNotInUTFRange(i).into());
                        }
                    }
                }
            },
            ArgFormat::Percent => {
                out.push('%');
            }
        }
        Ok(())
    }
}

// %(name)s or %s
enum NamedOrPositional {
    Named(String),
    Positional,
}

/// Implement Python `%` format strings.
pub struct Interpolation {
    /// String before first parameter
    init: String,
    /// Number of positional arguments
    positional_count: usize,
    /// Number of named arguments
    named_count: usize,
    /// Arguments followed by uninterpreted strings
    parameters: Vec<(NamedOrPositional, ArgFormat, String)>,
}

impl Interpolation {
    fn append_literal(&mut self, c: char) {
        if let Some(p) = self.parameters.last_mut() {
            p.2.push(c);
        } else {
            self.init.push(c)
        }
    }

    /// Parse a percent-interpolation string, returning an `Err` if the string is invalid.
    pub fn parse(format: &str) -> anyhow::Result<Self> {
        let mut result = Self {
            init: String::new(),
            positional_count: 0,
            named_count: 0,
            parameters: Vec::new(),
        };
        let mut chars = format.chars();
        while let Some(c) = chars.next() {
            if c != '%' {
                result.append_literal(c);
            } else {
                let next = chars
                    .next()
                    .ok_or(StringInterpolationError::UnexpectedEOFPercent)?;
                let (named_or_positional, format_char) = if next == '(' {
                    let mut name = String::new();
                    loop {
                        match chars.next() {
                            None => {
                                return Err(
                                    StringInterpolationError::UnexpectedEOFClosingParen.into()
                                );
                            }
                            Some(')') => {
                                break;
                            }
                            Some(c) => name.push(c),
                        }
                    }
                    (
                        NamedOrPositional::Named(name),
                        chars
                            .next()
                            .ok_or(StringInterpolationError::UnexpectedEOFPercent)?,
                    )
                } else {
                    (NamedOrPositional::Positional, next)
                };
                let format = match format_char {
                    's' => ArgFormat::Str,
                    'r' => ArgFormat::Repr,
                    'd' | 'i' => ArgFormat::Dec,
                    'o' => ArgFormat::Oct,
                    'x' => ArgFormat::HexLower,
                    'X' => ArgFormat::HexUpper,
                    'c' => ArgFormat::Char,
                    '%' => match named_or_positional {
                        NamedOrPositional::Positional => {
                            result.append_literal('%');
                            continue;
                        }
                        NamedOrPositional::Named(_) => {
                            // In both Python and Starlark Go implementations
                            // `%(n)%` consumes named argument, but
                            // `%%` does not consume positional argument.
                            // So `Percent` variant is added only when `ArgFormat` is `Named`.
                            ArgFormat::Percent
                        }
                    },
                    c => return Err(StringInterpolationError::UnknownSpecifier(c).into()),
                };
                match named_or_positional {
                    NamedOrPositional::Positional => {
                        result.positional_count += 1;
                    }
                    NamedOrPositional::Named(..) => {
                        result.named_count += 1;
                    }
                }
                result
                    .parameters
                    .push((named_or_positional, format, String::new()));
            }
        }
        Ok(result)
    }

    /// Apply a percent-interpolation string to a value.
    pub fn apply<'v>(self, argument: Value<'v>, heap: &'v Heap) -> anyhow::Result<String> {
        let mut r = self.init;
        let owned_tuple;
        let mut arg_iter: Box<dyn Iterator<Item = Value>> =
            if self.named_count > 0 && self.positional_count == 0 {
                box iter::empty()
            } else {
                match Tuple::from_value(argument) {
                    Some(x) => {
                        owned_tuple = x;
                        box owned_tuple.iter()
                    }
                    None => box iter::once(argument),
                }
            };
        for (named_or_positional, format, tail) in self.parameters {
            let arg = match named_or_positional {
                NamedOrPositional::Positional => match arg_iter.next() {
                    Some(a) => a,
                    None => return Err(StringInterpolationError::NotEnoughParameters.into()),
                },
                NamedOrPositional::Named(name) => argument.at(heap.alloc(name), heap)?,
            };
            format.format_arg(&mut r, arg)?;
            r.push_str(&tail);
        }

        if arg_iter.next().is_some() {
            return Err(StringInterpolationError::TooManyParameters.into());
        }

        Ok(r)
    }
}
