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

use crate::values::{tuple::Tuple, Value, ValueLike};
use gazebo::{cast, prelude::*};
use std::fmt::Write;
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
