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

//! Implementation of `repr()`.

use std::mem;

use crate::values::types::string::simd::{SwitchHaveSimd, Vector};

/// Check if any byte in the buffer is non-ASCII or need escape.
#[inline(always)]
unsafe fn need_escape<V: Vector>(chunk: V) -> bool {
    #[allow(clippy::many_single_char_names)]
    unsafe fn or5<V: Vector>(a: V, b: V, c: V, d: V, e: V) -> V {
        let ab = V::or(a, b);
        let cd = V::or(c, d);
        let abcd = V::or(ab, cd);
        V::or(abcd, e)
    }

    // Note `cmplt` is signed comparison.
    let any_control_or_non_ascii = chunk.cmplt(V::splat(32));
    let any_7f = chunk.cmpeq(V::splat(0x7f));
    let any_single_quote = chunk.cmpeq(V::splat(b'\''));
    let any_double_quote = chunk.cmpeq(V::splat(b'"'));
    let any_backslash = chunk.cmpeq(V::splat(b'\\'));

    let need_escape = or5(
        any_control_or_non_ascii,
        any_7f,
        any_single_quote,
        any_double_quote,
        any_backslash,
    );
    need_escape.movemask() != 0
}

pub(crate) fn string_repr(str: &str, buffer: &mut String) {
    // this method is surprisingly hot
    // so we first try and do a fast pass that only works for ASCII-only

    // Simple but definitely correct version
    fn loop_unicode(val: &str, buffer: &mut String) {
        for x in val.chars() {
            for c in x.escape_debug() {
                buffer.push(c);
            }
        }
    }

    // Process the ASCII prefix, bailing out to loop_unicode if we fail
    fn loop_ascii(val: &str, buffer: &mut String) {
        for (done, x) in val.as_bytes().iter().enumerate() {
            let x = *x;
            if x >= 128 {
                // bail out into a unicode-aware version
                loop_unicode(&val[done..], buffer);
                return;
            }
            // We enumerated all the bytes from 0..127.
            // The ones '"\ prepend an escape.
            // The ones below 31 or equal 127 print with a unicode escape.
            // Make sure we perfectly match escape_debug so if we take the
            // bailout its not a visible difference.
            if x <= 31 || x == 127 {
                for c in char::from(x).escape_debug() {
                    buffer.push(c)
                }
            } else {
                // safe because we know the following values are all lower-ascii bytes
                let byte_buffer = unsafe { buffer.as_mut_vec() };
                if x == b'"' || x == b'\'' || x == b'\\' {
                    byte_buffer.push(b'\\');
                }
                byte_buffer.push(x);
            }
        }
    }

    #[inline(always)]
    unsafe fn loop_ascii_simd<V: Vector>(val: &str, buffer: &mut String) {
        // `buffer` must have enough capacity to contain `val` if it does not need escaping
        // followed by trailing double quote.
        debug_assert!(buffer.capacity() - buffer.len() >= val.len() + 1);

        if val.len() < mem::size_of::<V>() {
            // Not enough length even for single SIMD iteration.
            return loop_ascii(val, buffer);
        }

        /// Push the tail of the vec to the buffer overwriting previously written buffer content
        /// (with identical content due to how this function is used).
        /// ```ignore
        /// buffer:   [       buffer.len         |  buffer rem capacity   ]
        /// vector:              [  overwriting  |  tail_len  ]
        /// ```
        #[inline(always)]
        unsafe fn push_vec_tail<V: Vector>(buffer: &mut String, vector: V, tail_len: usize) {
            debug_assert!(tail_len > 0);
            debug_assert!(tail_len <= mem::size_of::<V>());

            let new_buffer_len = buffer.len() + tail_len;

            // Write won't undershoot.
            debug_assert!(new_buffer_len >= mem::size_of::<V>());
            // Write won't overshoot.
            debug_assert!(new_buffer_len <= buffer.capacity());

            // Single store instruction.
            vector.store_unaligned(
                buffer
                    .as_bytes_mut()
                    .as_mut_ptr()
                    .add(new_buffer_len)
                    .sub(mem::size_of::<V>()),
            );
            buffer.as_mut_vec().set_len(new_buffer_len);
        }

        // Current offset in `val`.
        let mut val_offset = 0;

        // First process full chunks. Should take at least one iteration.
        debug_assert!(val.len() >= mem::size_of::<V>());
        while val_offset + mem::size_of::<V>() <= val.len() {
            let chunk = V::load_unaligned(val.as_ptr().add(val_offset) as *const _);

            if need_escape(chunk) {
                // NOTE(nga): two possible optimizations here:
                // * instead of `need_escape` flag, fetch position
                //   of the first character which need to be escaped, and write good prefix.
                // * if this chunk is ASCII, escape it and then return back to this loop.
                return loop_ascii(&val[val_offset..], buffer);
            }

            push_vec_tail(buffer, chunk, mem::size_of::<V>());

            val_offset += mem::size_of::<V>();
        }

        debug_assert!(val_offset >= mem::size_of::<V>());
        debug_assert!(val_offset + mem::size_of::<V>() > val.len());
        debug_assert!(val_offset % mem::size_of::<V>() == 0);

        // The remaining chunk is shorter than vector (or empty).
        if val_offset < val.len() {
            let chunk_len = val.len() - val_offset;
            debug_assert!(chunk_len > 0);
            debug_assert!(chunk_len < mem::size_of::<V>());

            debug_assert!(val.len() >= mem::size_of::<V>());
            // Last `chunk_len` bytes of `chunk` is new data,
            // and before `0..=chunk_len` of vec is data we have already written as is to `buffer`.
            let chunk = V::load_unaligned(val.as_ptr().add(val.len()).sub(mem::size_of::<V>()));

            if need_escape(chunk) {
                return loop_ascii(&val[val_offset..], buffer);
            }

            push_vec_tail(buffer, chunk, chunk_len);
        }
    }

    struct Switch<'a> {
        s: &'a str,
        buffer: &'a mut String,
    }

    impl<'a> SwitchHaveSimd<()> for Switch<'a> {
        fn no_simd(self) {
            loop_ascii(self.s, self.buffer)
        }

        fn simd<V: Vector>(self) {
            unsafe { loop_ascii_simd::<V>(self.s, self.buffer) }
        }
    }

    buffer.reserve(2 + str.len());
    buffer.push('"');
    Switch { s: str, buffer }.switch();
    buffer.push('"');
}

#[cfg(test)]
mod test {
    use std::mem;

    use crate::{
        assert,
        values::types::string::repr::{need_escape, string_repr},
    };

    #[test]
    fn test_to_repr() {
        assert::all_true(
            r#"
"\"\\t\\n\\'\\\"\"" == repr("\t\n'\"")
"\"Hello, 世界\"" == repr("Hello, 世界")
"#,
        );
    }

    #[test]
    fn test_string_repr() {
        fn test(expected: &str, input: &str) {
            let mut repr = String::new();
            string_repr(input, &mut repr);
            assert_eq!(expected, &repr);
        }
        // TODO(nga): should use \x escapes according to Starlark spec.
        test(r#""\u{12}""#, "\x12");
        test(r#""\u{7f}""#, "\x7f");
    }

    #[test]
    fn test_to_repr_long_smoke() {
        assert::all_true(
            r#"
'"0123456789abcdef"' == repr("0123456789abcdef")
'"0123456789\\nbcdef"' == repr("0123456789\nbcdef")
'"Мы, оглядываясь, видим лишь руины"' == repr("Мы, оглядываясь, видим лишь руины")
"#,
        )
    }

    fn string_repr_for_test(s: &str) -> String {
        let mut r = String::new();
        string_repr(s, &mut r);
        r
    }

    #[test]
    fn to_repr_sse() {
        for i in 0..0x80 {
            let s = String::from_utf8((0..33).map(|_| i as u8).collect()).unwrap();
            // Trigger debug assertions.
            string_repr_for_test(&s);
        }
    }

    #[test]
    fn to_repr_no_escape_all_lengths() {
        for len in 0..100 {
            let s = String::from_utf8((0..len).map(|i| b'0' + (i % 10)).collect()).unwrap();
            assert_eq!(format!("\"{}\"", s), string_repr_for_test(&s));
        }
    }

    #[test]
    fn to_repr_tail_escape_all_lengths() {
        for len in 0..100 {
            let s = String::from_utf8((0..len).map(|i| b'0' + (i % 10)).collect()).unwrap();
            assert_eq!(
                format!("\"{}\\n\"", s),
                string_repr_for_test(&format!("{}\n", s))
            );
        }
    }

    #[test]
    fn to_repr_middle_escape_all_lengths() {
        for len in 0..100 {
            let s = String::from_utf8((0..len).map(|i| b'0' + (i % 10)).collect()).unwrap();
            assert_eq!(
                format!("\"{}\\n{}\"", s, s),
                string_repr_for_test(&format!("{}\n{}", s, s))
            );
        }
    }

    // Test SSE version of `need_escape` works correctly.
    #[cfg(target_feature = "sse2")]
    #[test]
    fn test_need_escape() {
        use std::arch::x86_64::*;

        use crate::values::types::string::simd::Vector;

        unsafe fn load(s: &str) -> __m128i {
            assert_eq!(s.len(), mem::size_of::<__m128i>());
            <__m128i as Vector>::load_unaligned(s.as_ptr())
        }

        unsafe {
            assert!(!need_escape(load("0123456789abcdef")));
            assert!(!need_escape(load("0123456789abcde ")));
            assert!(need_escape(load("0123456789ab\x19def")));
            assert!(need_escape(load("0123456789abcde\n")));
            assert!(need_escape(load("0123456789ab\x7fdef")));
            assert!(need_escape(load("0123\x0456789ab\x02def")));
            assert!(need_escape(load("'123456789abcdef")));
            assert!(need_escape(load("0\"23456789abcdef")));
            assert!(need_escape(load("0123456 Я bcdef")));
        }
    }
}
