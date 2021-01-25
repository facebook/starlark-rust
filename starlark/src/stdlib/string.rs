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

//! Methods for the `string` type.

use crate as starlark;
use crate::{
    collections::SmallMap,
    environment::GlobalsBuilder,
    stdlib::{
        macros::{NoneOr, UnpackValue},
        util::convert_indices,
    },
    values::{Heap, TypedValue, Value, ValueError},
};
use anyhow::anyhow;
use gazebo::prelude::*;
use std::str::FromStr;

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
            None => Err(ValueError::KeyNotFound(n.to_owned().into_boxed_str().to_repr()).into()),
            Some(v) => Ok(conv(*v)),
        }
    }
}

// This does not exists in rust, split would cut the string incorrectly and
// split_whitespace cannot take a n parameter.
fn splitn_whitespace(s: &str, maxsplit: usize) -> Vec<String> {
    let mut v = Vec::new();
    let mut cur = String::new();
    let mut split = 1;
    let mut eat_ws = true;
    for c in s.chars() {
        if split >= maxsplit && !eat_ws {
            cur.push(c)
        } else if c.is_whitespace() {
            if !cur.is_empty() {
                v.push(cur);
                cur = String::new();
                split += 1;
                eat_ws = true;
            }
        } else {
            eat_ws = false;
            cur.push(c)
        }
    }
    if !cur.is_empty() {
        v.push(cur)
    }
    v
}

fn rsplitn_whitespace(s: &str, maxsplit: usize) -> Vec<String> {
    let mut v = Vec::new();
    let mut cur = String::new();
    let mut split = 1;
    let mut eat_ws = true;
    for c in s.chars().rev() {
        if split >= maxsplit && !eat_ws {
            cur.push(c)
        } else if c.is_whitespace() {
            if !cur.is_empty() {
                v.push(cur.chars().rev().collect());
                cur = String::new();
                split += 1;
                eat_ws = true;
            }
        } else {
            eat_ws = false;
            cur.push(c)
        }
    }
    if !cur.is_empty() {
        v.push(cur.chars().rev().collect());
    }
    v.reverse();
    v
}

struct StringOrTuple<'v>(Vec<&'v str>);

impl<'v> UnpackValue<'v> for StringOrTuple<'v> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        if let Some(s) = value.unpack_str() {
            Some(Self(vec![s]))
        } else {
            Some(Self(UnpackValue::unpack_value(value, heap)?))
        }
    }
}

#[starlark_module]
pub(crate) fn string_members(builder: &mut GlobalsBuilder) {
    /// [string.elems](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·elems
    /// ): returns an iterable of the bytes values of a string.
    ///
    /// `S.elems()` returns an iterable value containing the
    /// sequence of numeric bytes values in the string S.
    ///
    /// To materialize the entire sequence of bytes, apply `list(...)` to the
    /// result.
    ///
    /// Example:
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::is_true(r#"
    /// list("Hello, 世界".elems()) == [
    ///     72, 101, 108, 108, 111, 44, 32, 228, 184, 150, 231, 149, 140]
    /// # "#);
    /// ```
    fn elems(this: &str) -> Vec<i32> {
        // Note that we return a list here... Which is not equivalent to the go
        // implementation.
        Ok(this.as_bytes().map(|x| *x as i32))
    }

    /// [string.capitalize](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·capitalize
    /// ): returns a copy of string, with each first letter of a word in upper
    /// case.
    ///
    /// `S.capitalize()` returns a copy of string S with all Unicode letters
    /// that begin words changed to their title case.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "hello, world!".capitalize() == "Hello, World!"
    /// # "#);
    /// ```
    fn capitalize(this: &str) -> String {
        let mut last_space = true;
        let mut result = String::new();
        for c in this.chars() {
            if !c.is_alphanumeric() {
                last_space = true;
                result.push(c);
            } else {
                if last_space {
                    for c1 in c.to_uppercase() {
                        result.push(c1);
                    }
                } else {
                    result.push(c);
                }
                last_space = false;
            }
        }
        Ok(result)
    }

    /// [string.codepoints](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·codepoints
    /// ): returns an iterable of the unicode codepoint of a string.
    ///
    /// `S.codepoints()` returns an iterable value containing the
    /// sequence of integer Unicode code points encoded by the string S.
    /// Each invalid code within the string is treated as if it encodes the
    /// Unicode replacement character, U+FFFD.
    ///
    /// By returning an iterable, not a list, the cost of decoding the string
    /// is deferred until actually needed; apply `list(...)` to the result to
    /// materialize the entire sequence.
    ///
    /// Example:
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// list("Hello, 世界".codepoints()) == [72, 101, 108, 108, 111, 44, 32, 19990, 30028]
    /// # "#);
    /// ```
    fn codepoints(this: &str) -> Vec<i32> {
        // Note that we return a list here... Which is not equivalent to the go
        // implementation.
        let v: Vec<i32> = this.chars().map(|x| u32::from(x) as i32).collect();
        Ok(v)
    }

    /// [string.count](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·count
    /// ): count the number of occurrences of a string in another string.
    ///
    /// `S.count(sub[, start[, end]])` returns the number of occcurences of
    /// `sub` within the string S, or, if the optional substring indices
    /// `start` and `end` are provided, within the designated substring of S.
    /// They are interpreted according to Skylark's [indexing conventions](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#indexing).
    ///
    /// This implementation does not count occurence of `sub` in the string `S`
    /// that overlap other occurence of S (which can happen if some suffix of S
    /// is a prefix of S). For instance, `"abababa".count("aba")` returns 2
    /// for `[aba]a[aba]`, not counting the middle occurence: `ab[aba]ba`
    /// (this is following Python behavior).
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "hello, world!".count("o") == 2
    /// "abababa".count("aba") == 2
    /// "hello, world!".count("o", 7, 12) == 1  # in "world"
    /// # "#);
    /// ```
    fn count(
        this: &str,
        ref needle: &str,
        ref start @ NoneOr::None: NoneOr<i32>,
        ref end @ NoneOr::None: NoneOr<i32>,
    ) -> i32 {
        let (start, end) = convert_indices(this.len() as i32, start, end);
        let mut counter = 0i32;
        let mut s = this.get(start..end).unwrap();
        while let Some(offset) = s.find(needle) {
            counter += 1;
            s = s.get(offset + needle.len()..).unwrap_or("");
        }
        Ok(counter)
    }

    /// [string.endswith](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·endswith
    /// ): determine if a string ends with a given suffix.
    ///
    /// `S.endswith(suffix)` reports whether the string S has the specified
    /// suffix.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "filename.sky".endswith(".sky") == True
    /// # "#);
    /// ```
    fn endswith(this: &str, ref suffix: StringOrTuple) -> bool {
        for p in suffix.0.iter() {
            let p: &str = p;
            if this.ends_with(p) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// [string.find](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·find
    /// ): find a substring in a string.
    ///
    /// `S.find(sub[, start[, end]])` returns the index of the first
    /// occurrence of the substring `sub` within S.
    ///
    /// If either or both of `start` or `end` are specified,
    /// they specify a subrange of S to which the search should be restricted.
    /// They are interpreted according to Skylark's [indexing
    /// conventions](#indexing).
    ///
    /// If no occurrence is found, `found` returns -1.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "bonbon".find("on") == 1
    /// "bonbon".find("on", 2) == 4
    /// "bonbon".find("on", 2, 5) == -1
    /// # "#);
    /// ```
    fn find(
        this: &str,
        ref needle: &str,
        ref start @ NoneOr::None: NoneOr<i32>,
        ref end @ NoneOr::None: NoneOr<i32>,
    ) -> i32 {
        let (start, end) = convert_indices(this.len() as i32, start, end);
        if let Some(substring) = this.get(start..end) {
            if let Some(offset) = substring.find(needle) {
                return Ok((offset + start) as i32);
            }
        }
        Ok(-1)
    }

    /// [string.format](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·format
    /// ): format a string.
    ///
    /// `S.format(*args, **kwargs)` returns a version of the format string S
    /// in which bracketed portions `{...}` are replaced
    /// by arguments from `args` and `kwargs`.
    ///
    /// Within the format string, a pair of braces `{{` or `}}` is treated as
    /// a literal open or close brace.
    /// Each unpaired open brace must be matched by a close brace `}`.
    /// The optional text between corresponding open and close braces
    /// specifies which argument to use and how to format it, and consists of
    /// three components, all optional:
    /// a field name, a conversion preceded by '`!`', and a format specifier
    /// preceded by '`:`'.
    ///
    /// ```text
    /// {field}
    /// {field:spec}
    /// {field!conv}
    /// {field!conv:spec}
    /// ```
    ///
    /// The *field name* may be either a decimal number or a keyword.
    /// A number is interpreted as the index of a positional argument;
    /// a keyword specifies the value of a keyword argument.
    /// If all the numeric field names form the sequence 0, 1, 2, and so on,
    /// they may be omitted and those values will be implied; however,
    /// the explicit and implicit forms may not be mixed.
    ///
    /// The *conversion* specifies how to convert an argument value `x` to a
    /// string. It may be either `!r`, which converts the value using
    /// `repr(x)`, or `!s`, which converts the value using `str(x)` and is
    /// the default.
    ///
    /// The *format specifier*, after a colon, specifies field width,
    /// alignment, padding, and numeric precision.
    /// Currently it must be empty, but it is reserved for future use.
    ///
    /// Examples:
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// "a {} c".format(3) == "a 3 c"
    /// "a{x}b{y}c{}".format(1, x=2, y=3) == "a2b3c1"
    /// "a{}b{}c".format(1, 2) == "a1b2c"
    /// "({1}, {0})".format("zero", "one") == "(one, zero)"
    /// "Is {0!r} {0!s}?".format("heterological") == "Is \"heterological\" heterological?"
    /// # "#);
    /// ```
    fn format(this: &str, args: Vec<Value>, kwargs: SmallMap<&str, Value>) -> String {
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

    /// [string.index](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·index
    /// ): search a substring inside a string, failing on not found.
    ///
    /// `S.index(sub[, start[, end]])` returns the index of the first
    /// occurrence of the substring `sub` within S, like `S.find`, except
    /// that if the substring is not found, the operation fails.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "bonbon".index("on") == 1
    /// "bonbon".index("on", 2) == 4
    /// # "#);
    /// # starlark::assert::fail(r#"
    /// "bonbon".index("on", 2, 5)    # error: not found
    /// # "#, "not found");
    /// ```
    fn index(
        this: &str,
        ref needle: &str,
        ref start @ NoneOr::None: NoneOr<i32>,
        ref end @ NoneOr::None: NoneOr<i32>,
    ) -> i32 {
        let (start, end) = convert_indices(this.len() as i32, start, end);
        if let Some(substring) = this.get(start..end) {
            if let Some(offset) = substring.find(needle) {
                return Ok((offset + start) as i32);
            }
        }
        Err(anyhow!("Substring '{}' not found in '{}'", needle, this))
    }

    /// [string.isalnum](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isalnum
    /// ): test if a string is composed only of letters and digits.
    ///
    /// `S.isalnum()` reports whether the string S is non-empty and consists
    /// only Unicode letters and digits.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "base64".isalnum() == True
    /// "Catch-22".isalnum() == False
    /// # "#);
    /// ```
    fn isalnum(this: &str) -> bool {
        if this.is_empty() {
            return Ok(false);
        }
        for c in this.chars() {
            if !c.is_alphanumeric() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// [string.isalpha](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isalpha
    /// ): test if a string is composed only of letters.
    ///
    /// `S.isalpha()` reports whether the string S is non-empty and consists
    /// only of Unicode letters.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "ABC".isalpha() == True
    /// "Catch-22".isalpha() == False
    /// "".isalpha() == False
    /// # "#);
    /// ```
    fn isalpha(this: &str) -> bool {
        if this.is_empty() {
            return Ok(false);
        }
        for c in this.chars() {
            if !c.is_alphabetic() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// [string.isdigit](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isdigit
    /// ): test if a string is composed only of digits.
    ///
    /// `S.isdigit()` reports whether the string S is non-empty and consists
    /// only of Unicode digits.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "123".isdigit() == True
    /// "Catch-22".isdigit() == False
    /// "".isdigit() == False
    /// # "#);
    /// ```
    fn isdigit(this: &str) -> bool {
        if this.is_empty() {
            return Ok(false);
        }
        for c in this.chars() {
            if !c.is_numeric() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// [string.islower](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·islower
    /// ): test if all letters of a string are lowercase.
    ///
    /// `S.islower()` reports whether the string S contains at least one cased
    /// Unicode letter, and all such letters are lowercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "hello, world".islower() == True
    /// "Catch-22".islower() == False
    /// "123".islower() == False
    /// # "#);
    /// ```
    fn islower(this: &str) -> bool {
        let mut result = false;
        for c in this.chars() {
            if c.is_uppercase() {
                return Ok(false);
            } else if c.is_lowercase() {
                result = true;
            }
        }
        Ok(result)
    }

    /// [string.isspace](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isspace
    /// ): test if all characters of a string are whitespaces.
    ///
    /// `S.isspace()` reports whether the string S is non-empty and consists
    /// only of Unicode spaces.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "    ".isspace() == True
    /// "\r\t\n".isspace() == True
    /// "".isspace() == False
    /// # "#);
    /// ```
    fn isspace(this: &str) -> bool {
        if this.is_empty() {
            return Ok(false);
        }
        for c in this.chars() {
            if !c.is_whitespace() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// [string.istitle](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·istitle
    /// ): test if the string is title cased.
    ///
    /// `S.istitle()` reports whether the string S contains at least one cased
    /// Unicode letter, and all such letters that begin a word are in title
    /// case.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "Hello, World!".istitle() == True
    /// "Catch-22".istitle() == True
    /// "HAL-9000".istitle() == False
    /// "123".istitle() == False
    /// # "#);
    /// ```
    fn istitle(this: &str) -> bool {
        let mut last_space = true;
        let mut result = false;

        for c in this.chars() {
            if !c.is_alphabetic() {
                last_space = true;
            } else {
                if last_space {
                    if c.is_lowercase() {
                        return Ok(false);
                    }
                } else if c.is_uppercase() {
                    return Ok(false);
                }
                if c.is_alphabetic() {
                    result = true;
                }
                last_space = false;
            }
        }
        Ok(result)
    }

    /// [string.isupper](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isupper
    /// ): test if all letters of a string are uppercase.
    ///
    /// `S.isupper()` reports whether the string S contains at least one cased
    /// Unicode letter, and all such letters are uppercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "HAL-9000".isupper() == True
    /// "Catch-22".isupper() == False
    /// "123".isupper() == False
    /// # "#);
    /// ```
    fn isupper(this: &str) -> bool {
        let mut result = false;
        for c in this.chars() {
            if c.is_lowercase() {
                return Ok(false);
            } else if c.is_uppercase() {
                result = true;
            }
        }
        Ok(result)
    }

    /// [string.join](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·join
    /// ): join elements with a separator.
    ///
    /// `S.join(iterable)` returns the string formed by concatenating each
    /// element of its argument, with a copy of the string S between
    /// successive elements. The argument must be an iterable whose elements
    /// are strings.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// ", ".join(["one", "two", "three"]) == "one, two, three"
    /// "a".join("ctmrn".split_codepoints()) == "catamaran"
    /// # "#);
    /// ```
    fn join(this: &str, ref to_join: Value) -> String {
        let mut r = String::new();
        let to_join_iter = to_join.iterate(heap)?;
        for (index, item) in to_join_iter.iter().enumerate() {
            if index != 0 {
                r.push_str(this);
            }
            match item.unpack_str() {
                None => {
                    return Err(
                        ValueError::IncorrectParameterTypeNamed("to_join".to_owned()).into(),
                    );
                }
                Some(v) => r.push_str(v),
            }
        }
        Ok(r)
    }

    /// [string.lower](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·lower
    /// ): test if all letters of a string are lowercased.
    ///
    /// `S.lower()` returns a copy of the string S with letters converted to
    /// lowercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "Hello, World!".lower() == "hello, world!"
    /// # "#);
    /// ```
    fn lower(this: &str) -> String {
        Ok(this.to_lowercase())
    }

    /// [string.lstrip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·lstrip
    /// ): trim leading whitespaces.
    ///
    /// `S.lstrip()` returns a copy of the string S with leading whitespace
    /// removed.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "  hello  ".lstrip() == "hello  "
    /// "x!hello  ".lstrip("!x ") == "hello  "
    /// # "#);
    /// ```
    fn lstrip(this: &str, ref chars: Option<&str>) -> String {
        match chars {
            None => Ok(this.trim_start().to_owned()),
            Some(s) => Ok(this.trim_start_matches(|c| s.contains(c)).to_owned()),
        }
    }

    /// [string.partition](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·partition
    /// ): partition a string in 3 components
    ///
    /// `S.partition(x = " ")` splits string S into three parts and returns them
    /// as a tuple: the portion before the first occurrence of string `x`,
    /// `x` itself, and the portion following it.
    /// If S does not contain `x`, `partition` returns `(S, "", "")`.
    ///
    /// `partition` fails if `x` is not a string, or is the empty string.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "one/two/three".partition("/") == ("one", "/", "two/three")
    /// # "#);
    /// ```
    fn partition(this: &str, ref needle @ " ": &str) -> (String, String, String) {
        if needle.is_empty() {
            return Err(anyhow!("Empty separator cannot be used for partitioning"));
        }
        if let Some(offset) = this.find(needle) {
            let offset2 = offset + needle.len();
            Ok((
                this.get(..offset).unwrap().to_owned(),
                needle.to_owned(),
                this.get(offset2..).unwrap().to_owned(),
            ))
        } else {
            Ok((this.to_owned(), "".to_owned(), "".to_owned()))
        }
    }

    /// [string.replace](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·replace
    /// ): replace all occurences of a subtring.
    ///
    /// `S.replace(old, new[, count])` returns a copy of string S with all
    /// occurrences of substring `old` replaced by `new`. If the optional
    /// argument `count`, which must be an `int`, is non-negative, it
    /// specifies a maximum number of occurrences to replace.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "banana".replace("a", "o") == "bonono"
    /// "banana".replace("a", "o", 2) == "bonona"
    /// "# );
    /// # starlark::assert::fail(r#"
    /// "banana".replace("a", "o", -2)  # error: argument was negative
    /// "#, "argument was negative");
    /// ```
    fn replace(this: &str, ref old: &str, ref new: &str, ref count: Option<i32>) -> String {
        match count {
            Some(count) if count >= 0 => Ok(this.replacen(old, new, count as usize)),
            Some(count) => Err(anyhow!("Replace final argument was negative '{}'", count)),
            None => Ok(this.replace(old, new)),
        }
    }

    /// [string.rfind](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rfind
    /// ): find the last index of a substring.
    ///
    /// `S.rfind(sub[, start[, end]])` returns the index of the substring `sub`
    /// within S, like `S.find`, except that `rfind` returns the index of
    /// the substring's _last_ occurrence.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "bonbon".rfind("on") == 4
    /// "bonbon".rfind("on", None, 5) == 1
    /// "bonbon".rfind("on", 2, 5) == -1
    /// # "#);
    /// ```
    fn rfind(
        this: &str,
        ref needle: &str,
        ref start @ NoneOr::None: NoneOr<i32>,
        ref end @ NoneOr::None: NoneOr<i32>,
    ) -> i32 {
        let (start, end) = convert_indices(this.len() as i32, start, end);
        if let Some(substring) = this.get(start..end) {
            if let Some(offset) = substring.rfind(needle) {
                return Ok((offset + start) as i32);
            }
        }
        Ok(-1)
    }

    /// [string.rindex](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rindex
    /// ): find the last index of a substring, failing on not found.
    ///
    /// `S.rindex(sub[, start[, end]])` returns the index of the substring `sub`
    /// within S, like `S.index`, except that `rindex` returns the index of
    /// the substring's _last_ occurrence.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "bonbon".rindex("on") == 4
    /// "bonbon".rindex("on", None, 5) == 1  # in "bonbo"
    /// # "#);
    /// # starlark::assert::fail(r#"
    /// "bonbon".rindex("on", 2, 5) #   error: not found
    /// # "#, "not found");
    /// ```
    fn rindex(
        this: &str,
        ref needle: &str,
        ref start @ NoneOr::None: NoneOr<i32>,
        ref end @ NoneOr::None: NoneOr<i32>,
    ) -> i32 {
        let (start, end) = convert_indices(this.len() as i32, start, end);
        if let Some(substring) = this.get(start..end) {
            if let Some(offset) = substring.rfind(needle) {
                return Ok((offset + start) as i32);
            }
        }
        Err(anyhow!("Substring '{}' not found in '{}'", needle, this))
    }

    /// [string.rpartition](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rpartition
    /// ): partition a string in 3 elements.
    ///
    /// `S.rpartition([x = ' '])` is like `partition`, but splits `S` at the
    /// last occurrence of `x`.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "one/two/three".rpartition("/") == ("one/two", "/", "three")
    /// # "#);
    /// ```
    fn rpartition(this: &str, ref needle @ " ": &str) -> (String, String, String) {
        if needle.is_empty() {
            return Err(anyhow!("Empty separator cannot be used for partitioning"));
        }
        if let Some(offset) = this.rfind(needle) {
            let offset2 = offset + needle.len();
            Ok((
                this.get(..offset).unwrap().to_owned(),
                needle.to_owned(),
                this.get(offset2..).unwrap().to_owned(),
            ))
        } else {
            Ok(("".to_owned(), "".to_owned(), this.to_owned()))
        }
    }

    /// [string.rsplit](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rsplit
    /// ): splits a string into substrings.
    ///
    /// `S.rsplit([sep[, maxsplit]])` splits a string into substrings like
    /// `S.split`, except that when a maximum number of splits is specified,
    /// `rsplit` chooses the rightmost splits.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "banana".rsplit("n") == ["ba", "a", "a"]
    /// "banana".rsplit("n", 1) == ["bana", "a"]
    /// "one two  three".rsplit(None, 1) == ["one two", "three"]
    /// # "#);
    /// ```
    fn rsplit(
        this: &str,
        ref sep @ NoneOr::None: NoneOr<&str>,
        ref maxsplit @ NoneOr::None: NoneOr<i32>,
    ) -> Vec<String> {
        let maxsplit = match maxsplit.into_option() {
            None => None,
            Some(v) => {
                if v < 0 {
                    None
                } else {
                    Some((v + 1) as usize)
                }
            }
        };
        Ok(match sep.into_option() {
            None => match maxsplit {
                None => this.split_whitespace().map(ToOwned::to_owned).collect(),
                Some(maxsplit) => rsplitn_whitespace(this, maxsplit),
            },
            Some(sep) => {
                let mut v: Vec<String> = match maxsplit {
                    None => this.rsplit(sep).map(ToOwned::to_owned).collect(),
                    Some(maxsplit) => this.rsplitn(maxsplit, sep).map(ToOwned::to_owned).collect(),
                };
                v.reverse();
                v
            }
        })
    }

    /// [string.rstrip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rstrip
    /// ): trim trailing whitespace.
    ///
    /// `S.rstrip()` returns a copy of the string S with trailing whitespace
    /// removed.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "  hello  ".rstrip() == "  hello"
    /// "  hello!x".rstrip(" x!") == "  hello"
    /// # "#);
    /// ```
    fn rstrip(this: &str, ref chars: Option<&str>) -> String {
        match chars {
            None => Ok(this.trim_end().to_owned()),
            Some(s) => Ok(this.trim_end_matches(|c| s.contains(c)).to_owned()),
        }
    }

    /// [string.split](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·split
    /// ): split a string in substrings.
    ///
    /// `S.split([sep [, maxsplit]])` returns the list of substrings of S,
    /// splitting at occurrences of the delimiter string `sep`.
    ///
    /// Consecutive occurrences of `sep` are considered to delimit empty
    /// strings, so `'food'.split('o')` returns `['f', '', 'd']`.
    /// Splitting an empty string with a specified separator returns `['']`.
    /// If `sep` is the empty string, `split` fails.
    ///
    /// If `sep` is not specified or is `None`, `split` uses a different
    /// algorithm: it removes all leading spaces from S
    /// (or trailing spaces in the case of `rsplit`),
    /// then splits the string around each consecutive non-empty sequence of
    /// Unicode white space characters.
    ///
    /// If S consists only of white space, `split` returns the empty list.
    ///
    /// If `maxsplit` is given and non-negative, it specifies a maximum number
    /// of splits.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "one two  three".split() == ["one", "two", "three"]
    /// "one two  three".split(" ") == ["one", "two", "", "three"]
    /// "one two  three".split(None, 1) == ["one", "two  three"]
    /// "banana".split("n") == ["ba", "a", "a"]
    /// "banana".split("n", 1) == ["ba", "ana"]
    /// # "#);
    /// ```
    fn split(
        this: &str,
        ref sep @ NoneOr::None: NoneOr<&str>,
        ref maxsplit @ NoneOr::None: NoneOr<i32>,
    ) -> Vec<String> {
        let maxsplit = match maxsplit.into_option() {
            None => None,
            Some(v) => {
                if v < 0 {
                    None
                } else {
                    Some((v + 1) as usize)
                }
            }
        };
        Ok(match (sep.into_option(), maxsplit) {
            (None, None) => this.split_whitespace().map(ToOwned::to_owned).collect(),
            (None, Some(maxsplit)) => splitn_whitespace(this, maxsplit),
            (Some(sep), None) => this.split(sep).map(ToOwned::to_owned).collect(),
            (Some(sep), Some(maxsplit)) => {
                this.splitn(maxsplit, sep).map(ToOwned::to_owned).collect()
            }
        })
    }

    /// [string.split_codepoints](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·split_codepoints
    /// ): split a string into characters.
    ///
    /// `S.split_codepoints()` returns an iterable value containing the sequence
    /// of substrings of S that each encode a single Unicode code point.
    /// Each invalid code within the string is treated as if it encodes the
    /// Unicode replacement character, U+FFFD.
    ///
    /// By returning an iterable, not a list, the cost of decoding the string
    /// is deferred until actually needed; apply `list(...)` to the result to
    /// materialize the entire sequence.
    ///
    /// Example:
    ///
    /// Examples:
    ///
    /// ```
    /// starlark::assert::all_true(r#"
    /// list("Hello, 世界".split_codepoints()) == ["H", "e", "l", "l", "o", ",", " ", "世", "界"]
    /// # "#);
    /// ```
    fn split_codepoints(this: &str) -> Vec<String> {
        let v: Vec<String> = this.chars().map(|x| x.to_string()).collect();
        Ok(v)
    }

    /// [string.splitlines](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·splitlines
    /// ): return the list of lines of a string.
    ///
    /// `S.splitlines([keepends])` returns a list whose elements are the
    /// successive lines of S, that is, the strings formed by splitting S at
    /// line terminators ('\n', '\r' or '\r\n').
    ///
    /// The optional argument, `keepends`, is interpreted as a Boolean.
    /// If true, line terminators are preserved in the result, though
    /// the final element does not necessarily end with a line terminator.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "one\n\ntwo".splitlines() == ["one", "", "two"]
    /// "one\n\ntwo".splitlines(True) == ["one\n", "\n", "two"]
    /// "a\nb".splitlines() == ["a", "b"]
    /// # "#);
    /// ```
    fn splitlines(this: &str, ref keepends @ false: bool) -> Vec<String> {
        let mut s = this;
        let mut lines = Vec::new();
        loop {
            if let Some(x) = s.find(|x| x == '\n' || x == '\r') {
                let y = x;
                let x = match s.get(y..y + 2) {
                    Some("\r\n") => y + 2,
                    _ => y + 1,
                };
                if keepends {
                    lines.push(s.get(..x).unwrap())
                } else {
                    lines.push(s.get(..y).unwrap())
                }
                if x == s.len() {
                    return Ok(lines.owns());
                }
                s = s.get(x..).unwrap();
            } else {
                if !s.is_empty() {
                    lines.push(s);
                }
                return Ok(lines.owns());
            }
        }
    }

    /// [string.startswith](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·startswith
    /// ): test wether a string starts with a given prefix.
    ///
    /// `S.startswith(suffix)` reports whether the string S has the specified
    /// prefix.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "filename.sky".startswith("filename") == True
    /// # "#);
    /// ```
    fn startswith(this: &str, ref prefix: StringOrTuple) -> bool {
        for p in prefix.0.iter() {
            let p: &str = p;
            if this.starts_with(p) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// [string.strip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·strip
    /// ): trim leading and trailing whitespaces.
    ///
    /// `S.strip()` returns a copy of the string S with leading and trailing
    /// whitespace removed.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "  hello  ".strip() == "hello"
    /// "xxhello!!".strip("x!") == "hello"
    /// # "#);
    /// ```
    fn strip(this: &str, ref chars: Option<&str>) -> String {
        match chars {
            None => Ok(this.trim().to_owned()),
            Some(s) => Ok(this.trim_matches(|c| s.contains(c)).to_owned()),
        }
    }

    /// [string.title](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·title
    /// ): convert a string to title case.
    ///
    /// `S.lower()` returns a copy of the string S with letters converted to
    /// titlecase.
    ///
    /// Letters are converted to uppercase at the start of words, lowercase
    /// elsewhere.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "hElLo, WoRlD!".title() == "Hello, World!"
    /// # "#);
    /// ```
    fn title(this: &str) -> String {
        let mut last_space = true;
        let mut result = String::new();
        for c in this.chars() {
            if !c.is_alphabetic() {
                last_space = true;
                for c1 in c.to_lowercase() {
                    result.push(c1);
                }
            } else {
                if last_space {
                    for c1 in c.to_uppercase() {
                        result.push(c1);
                    }
                } else {
                    for c1 in c.to_lowercase() {
                        result.push(c1);
                    }
                }
                last_space = false;
            }
        }
        Ok(result)
    }

    /// [string.upper](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·upper
    /// ): convert a string to all uppercase.
    ///
    /// `S.lower()` returns a copy of the string S with letters converted to
    /// lowercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "Hello, World!".upper() == "HELLO, WORLD!"
    /// # "#);
    /// ```
    fn upper(this: &str) -> String {
        Ok(this.to_uppercase())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert;

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

    #[test]
    fn test_error_codes() {
        assert::fail(r#""bonbon".index("on", 2, 5)"#, "not found in");
        assert::fail(r#"("banana".replace("a", "o", -2))"#, "negative");
        assert::fail(r#""bonbon".rindex("on", 2, 5)"#, "not found in");
    }
}
