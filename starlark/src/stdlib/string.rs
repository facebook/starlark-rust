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

use crate::{
    self as starlark,
    environment::GlobalsBuilder,
    eval::Arguments,
    stdlib::util::convert_indices,
    values::{
        fast_string, interpolation, list::List, none::NoneOr, string, tuple::Tuple, UnpackValue,
        Value, ValueError, ValueOf,
    },
};
use anyhow::anyhow;
use gazebo::prelude::*;
use std::cmp;

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

enum StringOrTuple<'v> {
    String(&'v str),
    Tuple(Vec<&'v str>),
}

impl<'v> UnpackValue<'v> for StringOrTuple<'v> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        if let Some(s) = value.unpack_str() {
            Some(Self::String(s))
        } else {
            Some(Self::Tuple(
                Tuple::from_value(value)?
                    .iter()
                    .map(|x| x.unpack_str())
                    .collect::<Option<_>>()?,
            ))
        }
    }
}

#[starlark_module]
pub(crate) fn string_methods(builder: &mut GlobalsBuilder) {
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
    ///     "H", "e", "l", "l", "o", ",", " ", "世", "界"]
    /// # "#);
    /// ```
    fn elems(this: Value<'v>) -> Value<'v> {
        Ok(string::iterate_chars(this, heap))
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
    fn codepoints(this: Value<'v>) -> Value<'v> {
        Ok(string::iterate_codepoints(this, heap))
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
        mut this: &str,
        ref needle: &str,
        ref start @ NoneOr::None: NoneOr<i32>,
        ref end @ NoneOr::None: NoneOr<i32>,
    ) -> i32 {
        if !start.is_none() || !end.is_none() {
            let (start, end) = convert_indices(this.len() as i32, start, end);
            // FIXME: This unwrap can be triggered by users, should bubble up an error
            this = this.get(start..end).unwrap();
        }
        Ok(fast_string::count_matches(this, needle) as i32)
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
        match suffix {
            StringOrTuple::String(x) => Ok(this.ends_with(x)),
            StringOrTuple::Tuple(xs) => Ok(xs.iter().any(|x| this.ends_with(x))),
        }
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
    fn format(args: Arguments<'v, '_>) -> String {
        let iter = args.positions(heap)?;
        interpolation::format(
            args.this.unwrap().unpack_str().unwrap(),
            iter,
            args.names()?,
        )
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
    /// ", ".join([]) == ""
    /// ", ".join(("x", )) == "x"
    /// ", ".join(["one", "two", "three"]) == "one, two, three"
    /// "a".join("ctmrn".elems()) == "catamaran"
    /// # "#);
    /// ```
    fn join(this: &str, ref to_join: Value) -> Value<'v> {
        #[inline(always)]
        fn as_str<'v>(x: Value<'v>) -> anyhow::Result<&'v str> {
            match x.unpack_str() {
                None => Err(ValueError::IncorrectParameterTypeNamed("to_join".to_owned()).into()),
                Some(v) => Ok(v),
            }
        }

        to_join.with_iterator(heap, |it| {
            match it.next() {
                None => Ok(Value::new_empty_string()),
                Some(x1) => {
                    match it.next() {
                        None => {
                            as_str(x1)?;
                            // If there is a singleton we can avoid reallocation
                            Ok(x1)
                        }
                        Some(x2) => {
                            let s1 = as_str(x1)?;
                            let s2 = as_str(x2)?;
                            // guess towards the upper bound, since we throw away over-allocations quickly
                            // include a buffer (20 bytes)
                            let n = it.size_hint().0 + 2;
                            let guess =
                                (cmp::max(s1.len(), s2.len()) * n) + (this.len() * (n - 1)) + 20;
                            let mut r = String::with_capacity(guess);
                            r.push_str(s1);
                            r.push_str(this);
                            r.push_str(s2);
                            for x in it {
                                r.push_str(this);
                                r.push_str(as_str(x)?);
                            }
                            Ok(heap.alloc(r))
                        }
                    }
                }
            }
        })?
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
    /// `S.lstrip()` returns a copy of the string S with leading whitespace removed.
    /// In most cases instead of passing an argument you should use `removeprefix`.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "  hello  ".lstrip() == "hello  "
    /// "x!hello  ".lstrip("!x ") == "hello  "
    /// # "#);
    /// ```
    fn lstrip(this: &'v str, ref chars: Option<&str>) -> &'v str {
        match chars {
            None => Ok(this.trim_start()),
            Some(s) => Ok(this.trim_start_matches(|c| s.contains(c))),
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
    /// "one".partition("/") == ("one", "", "")
    /// # "#);
    /// ```
    fn partition(
        this: ValueOf<'v, &str>,
        ref needle: ValueOf<'v, &str>,
    ) -> (Value<'v>, Value<'v>, Value<'v>) {
        if needle.typed.is_empty() {
            return Err(anyhow!("Empty separator cannot be used for partitioning"));
        }
        if let Some(offset) = this.typed.find(needle.typed) {
            let offset2 = offset + needle.typed.len();
            Ok((
                heap.alloc(this.typed.get(..offset).unwrap()),
                needle.value,
                heap.alloc(this.typed.get(offset2..).unwrap()),
            ))
        } else {
            let empty = Value::new_empty_string();
            Ok((this.value, empty, empty))
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
    /// "one".rpartition("/") == ("", "", "one")
    /// # "#);
    /// ```
    fn rpartition(
        this: ValueOf<'v, &str>,
        ref needle: ValueOf<'v, &str>,
    ) -> (Value<'v>, Value<'v>, Value<'v>) {
        if needle.typed.is_empty() {
            return Err(anyhow!("Empty separator cannot be used for partitioning"));
        }
        if let Some(offset) = this.typed.rfind(needle.typed) {
            let offset2 = offset + needle.typed.len();
            Ok((
                heap.alloc(this.typed.get(..offset).unwrap()),
                needle.value,
                heap.alloc(this.typed.get(offset2..).unwrap()),
            ))
        } else {
            let empty = Value::new_empty_string();
            Ok((empty, empty, this.value))
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
    ) -> List<'v> {
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
        Ok(List::new(match sep.into_option() {
            None => match maxsplit {
                None => this.split_whitespace().map(|x| heap.alloc(x)).collect(),
                Some(maxsplit) => rsplitn_whitespace(this, maxsplit).map(|x| heap.alloc(x)),
            },
            Some(sep) => {
                let mut v: Vec<_> = match maxsplit {
                    None => this.rsplit(sep).map(|x| heap.alloc(x)).collect(),
                    Some(maxsplit) => this.rsplitn(maxsplit, sep).map(|x| heap.alloc(x)).collect(),
                };
                v.reverse();
                v
            }
        }))
    }

    /// [string.rstrip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rstrip
    /// ): trim trailing whitespace.
    ///
    /// `S.rstrip()` returns a copy of the string S with trailing whitespace removed.
    /// In most cases instead of passing an argument you should use `removesuffix`.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "  hello  ".rstrip() == "  hello"
    /// "  hello!x".rstrip(" x!") == "  hello"
    /// # "#);
    /// ```
    fn rstrip(this: &'v str, ref chars: Option<&str>) -> &'v str {
        match chars {
            None => Ok(this.trim_end()),
            Some(s) => Ok(this.trim_end_matches(|c| s.contains(c))),
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
    ) -> List<'v> {
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
        Ok(List::new(match (sep.into_option(), maxsplit) {
            (None, None) => this.split_whitespace().map(|x| heap.alloc(x)).collect(),
            (None, Some(maxsplit)) => splitn_whitespace(this, maxsplit).map(|x| heap.alloc(x)),
            (Some(sep), None) => {
                if sep.len() == 1 {
                    // If we are searching for a 1-byte string, we can provide a much faster path.
                    // Since it is one byte, given how UTF8 works, all the resultant slices must be UTF8 too.
                    let b = sep.as_bytes()[0];
                    let count = fast_string::count_matches_byte(this, b);
                    let mut res = Vec::with_capacity(count + 1);
                    res.extend(
                        this.as_bytes()
                            .split(|x| *x == b)
                            .map(|x| heap.alloc(unsafe { std::str::from_utf8_unchecked(x) })),
                    );
                    debug_assert_eq!(res.len(), count + 1);
                    res
                } else {
                    this.split(sep).map(|x| heap.alloc(x)).collect()
                }
            }
            (Some(sep), Some(maxsplit)) => {
                this.splitn(maxsplit, sep).map(|x| heap.alloc(x)).collect()
            }
        }))
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
    fn splitlines(this: &str, ref keepends @ false: bool) -> List<'v> {
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
                    lines.push(heap.alloc(s.get(..x).unwrap()))
                } else {
                    lines.push(heap.alloc(s.get(..y).unwrap()))
                }
                if x == s.len() {
                    return Ok(List::new(lines));
                }
                s = s.get(x..).unwrap();
            } else {
                if !s.is_empty() {
                    lines.push(heap.alloc(s));
                }
                return Ok(List::new(lines));
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
    /// "filename.sky".startswith("sky") == False
    /// 'abc'.startswith(('a', 'A')) == True
    /// 'ABC'.startswith(('a', 'A')) == True
    /// 'def'.startswith(('a', 'A')) == False
    /// # "#);
    /// ```
    fn startswith(this: &str, ref prefix: StringOrTuple) -> bool {
        match prefix {
            StringOrTuple::String(x) => Ok(this.starts_with(x)),
            StringOrTuple::Tuple(xs) => Ok(xs.iter().any(|x| this.starts_with(x))),
        }
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
    fn strip(this: &'v str, ref chars: Option<&str>) -> &'v str {
        match chars {
            None => Ok(this.trim()),
            Some(s) => Ok(this.trim_matches(|c| s.contains(c))),
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

    /// [string.removeprefix](
    /// https://docs.python.org/3.9/library/stdtypes.html#str.removeprefix
    /// ): remove a prefix from a string. _Not part of standard Starlark._
    ///
    /// If the string starts with the prefix string, return `string[len(prefix):]`.
    /// Otherwise, return a copy of the original string:
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "Hello, World!".removeprefix("Hello") == ", World!"
    /// "Hello, World!".removeprefix("Goodbye") == "Hello, World!"
    /// "Hello".removeprefix("Hello") == ""
    /// # "#);
    /// ```
    fn removeprefix(this: Value<'v>, ref prefix: &str) -> Value<'v> {
        let x = this.unpack_str().unwrap();
        if x.starts_with(prefix) && !prefix.is_empty() {
            Ok(heap.alloc(&x[prefix.len()..]))
        } else {
            Ok(this)
        }
    }

    /// [string.removesuffix](
    /// https://docs.python.org/3.9/library/stdtypes.html#str.removesuffix
    /// ): remove a prefix from a string. _Not part of standard Starlark._
    ///
    /// If the string starts with the prefix string, return `string[len(prefix):]`.
    /// Otherwise, return a copy of the original string:
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::all_true(r#"
    /// "Hello, World!".removesuffix("World!") == "Hello, "
    /// "Hello, World!".removesuffix("World") == "Hello, World!"
    /// "Hello".removesuffix("Hello") == ""
    /// # "#);
    /// ```
    fn removesuffix(this: Value<'v>, ref suffix: &str) -> Value<'v> {
        let x = this.unpack_str().unwrap();
        if x.ends_with(suffix) && !suffix.is_empty() {
            Ok(heap.alloc(&x[..x.len() - suffix.len()]))
        } else {
            Ok(this)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_error_codes() {
        assert::fail(r#""bonbon".index("on", 2, 5)"#, "not found in");
        assert::fail(r#"("banana".replace("a", "o", -2))"#, "negative");
        assert::fail(r#""bonbon".rindex("on", 2, 5)"#, "not found in");
    }

    #[test]
    fn test_opaque_iterator() {
        assert::is_true("type('foo'.elems()) != type([])");
        assert::is_true("type('foo'.codepoints()) != type([])");
    }
}
