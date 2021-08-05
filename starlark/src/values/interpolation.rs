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

use crate::values::{dict::Dict, tuple::Tuple, Value, ValueError, ValueLike};
use anyhow::anyhow;
use gazebo::{cast, prelude::*};
use std::{fmt::Write, str::FromStr};
use thiserror::Error;

/// Operator `%` format or evaluation errors
#[derive(Clone, Dupe, Debug, Error)]
enum StringInterpolationError {
    /// Interpolation parameter is too big for the format string.
    #[error("Too many arguments for format string")]
    TooManyParameters,
    /// Interpolation parameter is too small for the format string.
    #[error("Not enough arguments for format string")]
    NotEnoughParameters,
}

pub(crate) fn percent(format: &str, value: Value) -> anyhow::Result<String> {
    // For performance reasons, we treat format as a list of bytes
    // (which is fine, the only thing we care about are '%' and ASCII digits).
    // As a result, we accumulate into a Vec<u8>, which we know at any point
    // we are at the end or at a '%' must be a valid UTF8 buffer.

    // random guess as a baseline capacity
    let mut res: Vec<u8> = Vec::with_capacity(format.len() + 20);

    let tuple = Tuple::from_value(value);
    let one = &[value];
    let values = match &tuple {
        Some(xs) => xs.content.as_slice(),
        None => one,
    };
    let mut values = values.iter().copied();
    let mut next_value = || -> anyhow::Result<Value> {
        values
            .next()
            .ok_or_else(|| StringInterpolationError::NotEnoughParameters.into())
    };

    // because of the way format is defined, we can deal with it as bytes
    let mut format = format.as_bytes().iter().copied();
    while let Some(c) = format.next() {
        if c == b'%' {
            if let Some(c) = format.next() {
                let out: &mut String = unsafe { cast::ptr_mut(&mut res) };
                match c {
                    b'%' => res.push(b'%'),
                    b's' => {
                        let arg = next_value()?;
                        match arg.unpack_str() {
                            None => arg.collect_repr(out),
                            Some(s) => out.push_str(s),
                        }
                    }
                    b'r' => next_value()?.collect_repr(out),
                    b'd' => write!(out, "{}", next_value()?.to_int()?).unwrap(),
                    b'o' => {
                        let v = next_value()?.to_int()?;
                        write!(
                            out,
                            "{}{:o}",
                            if v < 0 { "-" } else { "" },
                            v.wrapping_abs() as u64
                        )
                        .unwrap();
                    }
                    b'x' => {
                        let v = next_value()?.to_int()?;
                        write!(
                            out,
                            "{}{:x}",
                            if v < 0 { "-" } else { "" },
                            v.wrapping_abs() as u64
                        )
                        .unwrap();
                    }
                    b'X' => {
                        let v = next_value()?.to_int()?;
                        write!(
                            out,
                            "{}{:X}",
                            if v < 0 { "-" } else { "" },
                            v.wrapping_abs() as u64
                        )
                        .unwrap()
                    }
                    c => {
                        res.push(b'%');
                        res.push(c);
                    }
                }
            } else {
                res.push(b'%');
            }
        } else {
            res.push(c);
        }
    }
    if values.next().is_some() {
        Err(StringInterpolationError::TooManyParameters.into())
    } else {
        Ok(unsafe { String::from_utf8_unchecked(res) })
    }
}

/// The format string can either have explicit indices,
/// or grab things sequentially, but not both.
/// FormatArgs knows which we are doing and keeps them in mind.
struct FormatArgs<'v, T: Iterator<Item = Value<'v>>> {
    // Initially we have the iterator set and the args empty.
    // If we ever ask by index, we decant the iterator into args.
    iterator: T,
    args: Vec<Value<'v>>,
    by_index: bool,
    by_order: bool,
}

impl<'v, T: Iterator<Item = Value<'v>>> FormatArgs<'v, T> {
    fn new(iterator: T) -> Self {
        Self {
            iterator,
            args: Vec::new(),
            by_index: false,
            by_order: false,
        }
    }

    fn next_ordered(&mut self) -> anyhow::Result<Value<'v>> {
        if self.by_index {
            Err(anyhow!(
                "Cannot mix manual field specification and automatic field numbering in format string",
            ))
        } else {
            self.by_order = true;
            match self.iterator.next() {
                None => Err(anyhow!("Not enough parameters in format string")),
                Some(x) => Ok(x),
            }
        }
    }

    fn by_index(&mut self, index: usize) -> anyhow::Result<Value<'v>> {
        if self.by_order {
            Err(anyhow!(
                "Cannot mix manual field specification and automatic field numbering in format string",
            ))
        } else {
            if !self.by_index {
                self.args.extend(&mut self.iterator);
                self.by_index = true;
            }
            match self.args.get(index) {
                None => Err(ValueError::IndexOutOfBound(index as i32).into()),
                Some(v) => Ok(*v),
            }
        }
    }
}

pub(crate) fn format<'v>(
    this: &str,
    args: impl Iterator<Item = Value<'v>>,
    kwargs: Dict<'v>,
) -> anyhow::Result<String> {
    let mut args = FormatArgs::new(args);
    let mut result = String::new();
    let mut capture = String::new();
    for c in this.chars() {
        match (c, capture.as_str()) {
            ('{', "") | ('}', "") => capture.push(c),
            (.., "") => result.push(c),
            ('{', "{") => {
                result.push('{');
                capture.clear();
            }
            ('{', "}") => return Err(anyhow!("Standalone '}}' in format string `{}`", this)),
            ('{', ..) => return Err(anyhow!("Unmatched '{' in format string")),
            ('}', "}") => {
                result.push('}');
                capture.clear();
            }
            ('}', ..) => {
                result += &format_capture(&capture, &mut args, &kwargs)?;
                capture.clear();
            }
            (.., "}") => return Err(anyhow!("Standalone '}}' in format string `{}`", this)),
            _ => capture.push(c),
        }
    }
    match capture.as_str() {
        "}" => Err(anyhow!("Standalone '}}' in format string `{}`", this)),
        "" => Ok(result),
        _ => Err(anyhow!("Unmatched '{' in format string")),
    }
}

fn format_capture<'v, T: Iterator<Item = Value<'v>>>(
    capture: &str,
    args: &mut FormatArgs<'v, T>,
    kwargs: &Dict,
) -> anyhow::Result<String> {
    let (n, conv) = {
        if let Some(x) = capture.find('!') {
            (capture.get(1..x).unwrap(), capture.get(x + 1..).unwrap())
        } else {
            (capture.get(1..).unwrap(), "s")
        }
    };
    let conv_s = |x: Value| x.to_str();
    let conv_r = |x: Value| x.to_repr();
    let conv: &dyn Fn(Value) -> String = match conv {
        "s" => &conv_s,
        "r" => &conv_r,
        c => {
            return Err(anyhow!(
                concat!(
                    "'{}' is not a valid format string specifier, only ",
                    "'s' and 'r' are valid specifiers",
                ),
                c
            ));
        }
    };
    if n.is_empty() {
        Ok(conv(args.next_ordered()?))
    } else if n.chars().all(|c| c.is_ascii_digit()) {
        let i = usize::from_str(n).unwrap();
        Ok(conv(args.by_index(i)?))
    } else {
        if let Some(x) = n.chars().find(|c| match c {
            '.' | ',' | '[' | ']' => true,
            _ => false,
        }) {
            return Err(anyhow!(
                "Invalid character '{}' inside replacement field",
                x
            ));
        }
        match kwargs.get_str(n) {
            None => Err(ValueError::KeyNotFound(n.to_owned()).into()),
            Some(v) => Ok(conv(v)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{collections::SmallMap, values::Heap};

    #[test]
    fn test_format_capture() {
        let heap = Heap::new();
        let original_args = vec![heap.alloc("1"), heap.alloc("2"), heap.alloc("3")];
        let mut args = FormatArgs::new(original_args.iter().copied());
        let mut kwargs = SmallMap::new();

        kwargs.insert_hashed(heap.alloc_str_hashed("a"), heap.alloc("x"));
        kwargs.insert_hashed(heap.alloc_str_hashed("b"), heap.alloc("y"));
        kwargs.insert_hashed(heap.alloc_str_hashed("c"), heap.alloc("z"));
        let kwargs = Dict::new(kwargs);
        assert_eq!(format_capture("{", &mut args, &kwargs,).unwrap(), "1");
        assert_eq!(format_capture("{!s", &mut args, &kwargs,).unwrap(), "2");
        assert_eq!(format_capture("{!r", &mut args, &kwargs,).unwrap(), "\"3\"");
        assert_eq!(
            format_capture("{a!r", &mut args, &kwargs,).unwrap(),
            "\"x\""
        );
        assert_eq!(format_capture("{a!s", &mut args, &kwargs,).unwrap(), "x");
        assert!(format_capture("{1", &mut args, &kwargs,).is_err());
        let mut args = FormatArgs::new(original_args.iter().copied());
        assert_eq!(format_capture("{1", &mut args, &kwargs,).unwrap(), "2");
        assert!(format_capture("{", &mut args, &kwargs,).is_err());
    }
}
