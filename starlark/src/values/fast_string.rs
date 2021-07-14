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

//! Our string operations (indexing) are O(n) because of our current representation.
//! There are plans afoot to change that, but in the meantime let's use fast algorithms
//! to make up some of the difference.

use std::{cmp::min, str};

#[inline(always)]
fn is_1byte(x: u8) -> bool {
    x & 0x80 == 0
}

#[inline(always)]
fn is_1bytes(x: u64) -> bool {
    x & 0x8080808080808080 == 0
}

/// Skip at most n 1byte characters from the prefix of the string, return how many you skipped.
/// The result will be between 0 and n.
fn skip_at_most_1byte(x: &str, n: usize) -> usize {
    // Multi-byte UTF8 characters have 0x80 set.
    // We first process enough characters so we align on an 8-byte boundary,
    // then process 8 bytes at a time.
    // If we see a higher value, we bail to the standard Rust code.
    // It is possible to do faster with population count, but we don't expect many real UTF8 strings.
    // (c.f. https://github.com/haskell-foundation/foundation/blob/master/foundation/cbits/foundation_utf8.c)

    // Same function, but returning the end of the string
    fn f(x: &str, n: usize) -> *const u8 {
        let leading = min(x.as_ptr().align_offset(8), n);
        let trailing = (n - leading) % 8;
        let loops = (n - leading) / 8;

        // Rather than flip between string and pointer, we stick to working with the pointer
        let mut p = x.as_ptr();

        // Loop over 1 byte at a time until we reach alignment
        for _ in 0..leading {
            if is_1byte(unsafe { *p }) {
                p = unsafe { p.add(1) };
            } else {
                return p;
            }
        }

        // Loop over 8 bytes at a time, until we reach the end
        let mut p = p as *const u64;
        for _ in 0..loops {
            if is_1bytes(unsafe { *p }) {
                p = unsafe { p.add(1) };
            } else {
                return p as *const u8;
            }
        }

        // Mop up all trailing bytes
        let mut p = p as *const u8;
        for _ in 0..trailing {
            if is_1byte(unsafe { *p }) {
                p = unsafe { p.add(1) };
            } else {
                return p;
            }
        }
        return p;
    }

    unsafe { f(x, n).offset_from(x.as_ptr()) as usize }
}

/// Find the character at position `i`.
pub fn at(x: &str, i: usize) -> Option<char> {
    let n = skip_at_most_1byte(x, min(i, x.len()));
    let s = unsafe { str::from_utf8_unchecked(&x.as_bytes()[n..]) };
    s.chars().nth(i - n)
}

/// Find the length of the string in characters.
/// If the length matches the length in bytes, the string must be 7bit ASCII.
pub fn len(x: &str) -> usize {
    let n = skip_at_most_1byte(x, x.len());
    if n == x.len() {
        n // All 1 byte
    } else {
        unsafe { str::from_utf8_unchecked(&x.as_bytes()[n..]) }
            .chars()
            .count()
            + n
    }
}

/// Find the number of times a `needle` byte occurs within a string.
/// If the needle represents a complete character, this will be equivalent to doing
/// search for that character in the string.
pub fn count_matches_byte(x: &str, needle: u8) -> usize {
    x.as_bytes().iter().filter(|x| **x == needle).count()
}

/// Find the number of times a `needle` occurs within a string, non-overlapping.
pub fn count_matches(x: &str, needle: &str) -> usize {
    if needle.len() == 1 {
        // If we are searching for a 1-byte string, we can provide a much faster path.
        // Since it is one byte, given how UTF8 works, all the resultant slices must be UTF8 too.
        count_matches_byte(x, needle.as_bytes()[0])
    } else {
        x.matches(needle).count()
    }
}

/// Apppend two strings together.
/// Inline because it's a hot-spot, and often length checks will be done just before.
#[inline]
pub fn append(x: &str, y: &str) -> String {
    // Optimised based on https://github.com/hoodie/concatenation_benchmarks-rs
    let mut s = String::with_capacity(x.len() + y.len());
    s.push_str(x);
    s.push_str(y);
    s
}
