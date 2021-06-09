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

use crate::{
    collections::SmallMap,
    values::{tuple::Tuple, StarlarkValue, Value, ValueError, ValueLike},
};
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
    if next_value().is_ok() {
        Err(StringInterpolationError::TooManyParameters.into())
    } else {
        Ok(unsafe { String::from_utf8_unchecked(res) })
    }
}

pub(crate) fn format(
    this: &str,
    args: Vec<Value>,
    kwargs: SmallMap<&str, Value>,
) -> anyhow::Result<String> {
    let mut it = args.iter().copied();
    let mut captured_by_index = false;
    let mut captured_by_order = false;
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
                result += &format_capture(
                    &capture,
                    &mut it,
                    &mut captured_by_index,
                    &mut captured_by_order,
                    &args,
                    &kwargs,
                )?;
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
    it: &mut T,
    captured_by_index: &mut bool,
    captured_by_order: &mut bool,
    args: &[Value],
    kwargs: &SmallMap<&str, Value>,
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
        if *captured_by_index {
            return Err(anyhow!(
                "Cannot mix manual field specification and automatic field numbering in format string",
            ));
        } else {
            *captured_by_order = true;
            if let Some(x) = it.next() {
                return Ok(conv(x));
            } else {
                return Err(anyhow!("Not enough parameters in format string"));
            }
        }
    } else if n.chars().all(|c| c.is_ascii_digit()) {
        if *captured_by_order {
            return Err(anyhow!(
                "Cannot mix manual field specification and automatic field numbering in format string",
            ));
        } else {
            *captured_by_index = true;
            let i = i32::from_str(n).unwrap();
            if i < 0 || i >= (args.len() as i32) {
                return Err(ValueError::IndexOutOfBound(i).into());
            }
            Ok(conv(args[i as usize]))
        }
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
        match kwargs.get(n) {
            None => Err(ValueError::KeyNotFound(Box::<str>::from(n).to_repr()).into()),
            Some(v) => Ok(conv(*v)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::Heap;

    #[test]
    fn test_format_capture() {
        let heap = Heap::new();
        let args = vec![heap.alloc("1"), heap.alloc("2"), heap.alloc("3")];
        let mut kwargs = SmallMap::new();
        let it = heap.alloc(args.clone());
        let it = it.iterate(&heap).unwrap();
        let mut it = it.iter();
        let mut captured_by_index = false;
        let mut captured_by_order = false;

        kwargs.insert("a", heap.alloc("x"));
        kwargs.insert("b", heap.alloc("y"));
        kwargs.insert("c", heap.alloc("z"));
        assert_eq!(
            format_capture(
                "{",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "1"
        );
        assert_eq!(
            format_capture(
                "{!s",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "2"
        );
        assert_eq!(
            format_capture(
                "{!r",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "\"3\""
        );
        assert_eq!(
            format_capture(
                "{a!r",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "\"x\""
        );
        assert_eq!(
            format_capture(
                "{a!s",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "x"
        );
        assert!(
            format_capture(
                "{1",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .is_err()
        );
        captured_by_order = false;
        let it = heap.alloc(args.clone());
        let it = it.iterate(&heap).unwrap();
        let mut it = it.iter();
        assert_eq!(
            format_capture(
                "{1",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "2"
        );
        assert!(
            format_capture(
                "{",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .is_err()
        );
    }
}
