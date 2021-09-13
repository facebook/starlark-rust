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

//! The string type. All strings must be valid UTF8.

use crate as starlark;
use crate::{
    collections::{BorrowHashed, SmallHashResult},
    environment::{Globals, GlobalsStatic},
    values::{
        fast_string, index::apply_slice, interpolation, AllocFrozenValue, AllocValue, ComplexValue,
        Freezer, FrozenHeap, FrozenValue, Heap, SimpleValue, StarlarkValue, Trace, UnpackValue,
        Value, ValueError, ValueLike,
    },
};
use gazebo::{any::AnyLifetime, coerce::Coerce, prelude::OptionExt};
use std::{
    cmp,
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    fmt,
    fmt::Debug,
    hash::{Hash, Hasher},
    slice, str,
    sync::atomic,
};

/// The result of calling `type()` on strings.
pub const STRING_TYPE: &str = "string";

/// A pointer to this type represents a Starlark string.
/// Use of this type is discouraged and not considered stable.
#[derive(AnyLifetime)]
#[repr(C)] // We want the body to come after len
pub struct StarlarkStr {
    len: usize,
    // Lazily-initialized cached hash code.
    // TODO(nga): when this field added, Starlark memory consumption
    //   increased by approximately 0.7%. So if we could change
    //   both `hash` and `len` fields to 32-bit, we would save 0.7% memory.
    hash: atomic::AtomicU64,
    // Followed by an unsized block, meaning this type is unsized.
    // But we can't mark it as such since we really want &StarlarkStr to
    // take up only one word.
    body: [u8; 0],
}

impl Debug for StarlarkStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.unpack().fmt(f)
    }
}

impl StarlarkStr {
    /// Unsafe because if you do `unpack` on this it will blow up
    pub(crate) const unsafe fn new(len: usize) -> Self {
        Self {
            len,
            hash: atomic::AtomicU64::new(0),
            body: [],
        }
    }

    pub fn unpack(&self) -> &str {
        unsafe {
            let slice = slice::from_raw_parts(self.body.as_ptr(), self.len);
            str::from_utf8_unchecked(slice)
        }
    }

    fn get_hash_64(&self) -> u64 {
        // Note relaxed load and store are practically non-locking memory operations.
        let hash = self.hash.load(atomic::Ordering::Relaxed);
        if hash != 0 {
            hash
        } else {
            let mut s = DefaultHasher::new();
            hash_string_value(self.unpack(), &mut s);
            let hash = s.finish();
            // If hash is zero, we are unlucky, but it is highly improbable.
            self.hash.store(hash, atomic::Ordering::Relaxed);
            hash
        }
    }

    pub fn as_str_hashed(&self) -> BorrowHashed<str> {
        BorrowHashed::new_unchecked(
            SmallHashResult::new_unchecked(self.get_hash_64()),
            self.unpack(),
        )
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'v> AllocValue<'v> for String {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(self.as_str())
    }
}

impl<'v> AllocValue<'v> for char {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_char(self)
    }
}

impl<'v> AllocValue<'v> for &'_ String {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(self.as_str())
    }
}

impl<'v> AllocValue<'v> for &'_ str {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(self)
    }
}

impl<'v> UnpackValue<'v> for &'v str {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        value.unpack_str()
    }
}

impl<'v> UnpackValue<'v> for String {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        value.unpack_str().map(ToOwned::to_owned)
    }
}

/// How to hash a string in a way that is compatible with Value
pub(crate) fn hash_string_value<H: Hasher>(x: &str, state: &mut H) {
    x.hash(state)
}

/// Hash a string in a way compatible with Value
pub(crate) fn hash_string_result(x: &str) -> SmallHashResult {
    SmallHashResult::new(x)
}

pub(crate) fn json_escape(x: &str) -> String {
    let mut escaped = Vec::with_capacity(x.len() + 2);
    escaped.push(b'\"');
    for c in x.bytes() {
        // Escape as per ECMA-404 standard
        match c {
            b'\\' => escaped.extend(b"\\\\".iter()),
            b'"' => escaped.extend(b"\\\"".iter()),
            0x08u8 => escaped.extend(b"\\b".iter()),
            0x0Cu8 => escaped.extend(b"\\f".iter()),
            b'\n' => escaped.extend(b"\\n".iter()),
            b'\r' => escaped.extend(b"\\r".iter()),
            b'\t' => escaped.extend(b"\\t".iter()),
            x => escaped.push(x),
        }
    }
    escaped.push(b'\"');
    unsafe { String::from_utf8_unchecked(escaped) }
}

impl SimpleValue for StarlarkStr {}

impl<'v> StarlarkValue<'v> for StarlarkStr {
    starlark_type!(STRING_TYPE);

    fn get_methods(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.methods(crate::stdlib::string::string_methods)
    }

    fn collect_repr(&self, buffer: &mut String) {
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
                // The ones below 31 print with a unicode escape.
                // Make sure we perfectly match escape_debug so if we take the
                // bailout its not a visible difference.
                if x <= 31 {
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

        buffer.reserve(2 + self.len());
        buffer.push('"');
        loop_ascii(self.unpack(), buffer);
        buffer.push('"');
    }

    fn to_json(&self) -> anyhow::Result<String> {
        Ok(json_escape(self.unpack()))
    }

    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        Ok(self.get_hash_64())
    }

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        if let Some(other) = other.unpack_str() {
            Ok(*self.unpack() == *other)
        } else {
            Ok(false)
        }
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        if let Some(other) = other.unpack_str() {
            Ok(self.unpack().cmp(other))
        } else {
            ValueError::unsupported_with(self, "cmp()", other)
        }
    }

    fn at(&self, index: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        // This method is disturbingly hot. Use the logic from `convert_index`,
        // but modified to be UTF8 string friendly.
        let s = self.unpack();
        match index.to_int() {
            Err(_) => Err(ValueError::IncorrectParameterType.into()),
            Ok(i) => {
                if i >= 0 {
                    match fast_string::at(s, i as usize) {
                        None => Err(ValueError::IndexOutOfBound(i).into()),
                        Some(c) => Ok(heap.alloc(c)),
                    }
                } else {
                    let len_chars = fast_string::len(s);
                    let ind = (-i) as usize; // Index from the end, minimum of 1
                    if ind > len_chars {
                        Err(ValueError::IndexOutOfBound(i).into())
                    } else if len_chars == s.len() {
                        // We are a 7bit ASCII string, so take the fast-path
                        Ok(heap.alloc(s.as_bytes()[len_chars - ind] as char))
                    } else {
                        Ok(heap.alloc(fast_string::at(s, len_chars - ind).unwrap()))
                    }
                }
            }
        }
    }

    fn extra_memory(&self) -> usize {
        // We don't include the extra_memory for the size because it is
        // allocated inline in the Starlark heap (which knows about it),
        // not on the malloc heap.
        0
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(fast_string::len(self.unpack()) as i32)
    }

    fn is_in(&self, other: Value) -> anyhow::Result<bool> {
        match other.unpack_str() {
            Some(s) => {
                let me = self.unpack();
                if s.len() == 1 {
                    Ok(me.as_bytes().contains(&s.as_bytes()[0]))
                } else {
                    Ok(me.contains(s))
                }
            }
            None => Err(ValueError::IncorrectParameterType.into()),
        }
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        let s = self.unpack();
        if matches!(stride, Some(stride) if stride.unpack_int() != Some(1)) {
            // The stride case is super rare and super complex, so let's do something inefficient but safe
            let xs = s.chars().collect::<Vec<_>>();
            let xs = apply_slice(&xs, start, stop, stride)?;
            return Ok(heap.alloc(xs.into_iter().collect::<String>()));
        }

        // We know stride == 1, so can ignore it
        let start = start.map_or(Ok(0), |v| v.to_int())?;
        let stop = stop.try_map(|v| v.to_int())?;

        if start >= 0 {
            match stop {
                None => return Ok(heap.alloc_str(fast_string::split_at(s, start as usize).1)),
                Some(stop) if stop >= 0 => {
                    let s = fast_string::split_at(s, start as usize).1;
                    let s = fast_string::split_at(s, cmp::max(0, stop - start) as usize).0;
                    return Ok(heap.alloc_str(s));
                }
                _ => {}
            }
        }
        let len_chars = fast_string::len(s);
        let adjust = |x| {
            cmp::min(
                if x < 0 {
                    cmp::max(0, x + (len_chars as i32))
                } else {
                    x
                },
                len_chars as i32,
            ) as usize
        };
        let start = adjust(start);
        let stop = adjust(stop.unwrap_or(len_chars as i32));

        if start >= stop {
            Ok(heap.alloc_str(""))
        } else if s.len() == len_chars {
            // ASCII fast-path
            Ok(heap.alloc_str(s.get(start..stop).unwrap()))
        } else {
            let s = fast_string::split_at(s, start).1;
            let s = if stop == len_chars {
                s
            } else {
                fast_string::split_at(s, cmp::max(0, stop - start)).0
            };
            return Ok(heap.alloc_str(s));
        }
    }

    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other_str) = other.unpack_str() {
            if self.is_empty() {
                Ok(other)
            } else {
                Ok(heap.alloc_str_concat(self.unpack(), other_str))
            }
        } else {
            ValueError::unsupported_with(self, "+", other)
        }
    }

    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_int() {
            Some(l) => {
                let s = self.unpack();
                let mut result = String::with_capacity(s.len() * cmp::max(0, l) as usize);
                for _i in 0..l {
                    result.push_str(s)
                }
                Ok(heap.alloc(result))
            }
            None => Err(ValueError::IncorrectParameterType.into()),
        }
    }

    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(heap.alloc(interpolation::percent(self.unpack(), other)?))
    }
}

impl AllocFrozenValue for String {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_str(self.as_str())
    }
}

impl<'v, 'a> AllocFrozenValue for &'a str {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_str(self)
    }
}

/// An opaque iterator over a string, produced by elems/codepoints
#[derive(Debug, Trace, Coerce)]
#[repr(C)]
struct StringIteratorGen<V> {
    string: V,
    produce_char: bool, // if not char, then int
}

pub(crate) fn iterate_chars<'v>(string: Value<'v>, heap: &'v Heap) -> Value<'v> {
    heap.alloc(StringIterator {
        string,
        produce_char: true,
    })
}

pub(crate) fn iterate_codepoints<'v>(string: Value<'v>, heap: &'v Heap) -> Value<'v> {
    heap.alloc(StringIterator {
        string,
        produce_char: false,
    })
}

starlark_complex_value!(StringIterator);

impl<'v, T: ValueLike<'v>> StarlarkValue<'v> for StringIteratorGen<T>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!("iterator");

    fn iterate<'a>(
        &'a self,
        heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'a>>
    where
        'v: 'a,
    {
        let s = self.string.to_value().unpack_str().unwrap().chars();
        if self.produce_char {
            Ok(box s.map(move |x| heap.alloc(x)))
        } else {
            Ok(box s.map(|x| Value::new_int(u32::from(x) as i32)))
        }
    }

    fn with_iterator(
        &self,
        heap: &'v Heap,
        f: &mut dyn FnMut(&mut dyn Iterator<Item = Value<'v>>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        let s = self.string.to_value().unpack_str().unwrap().chars();
        if self.produce_char {
            f(&mut s.map(|x| heap.alloc(x)))
        } else {
            f(&mut s.map(|x| Value::new_int(u32::from(x) as i32)))
        }
    }
}

impl<'v> ComplexValue<'v> for StringIterator<'v> {
    type Frozen = FrozenStringIterator;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        Ok(FrozenStringIterator {
            string: freezer.freeze(self.string)?,
            produce_char: self.produce_char,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        assert,
        values::{index::apply_slice, Heap, Value, ValueLike},
    };

    #[test]
    fn test_string_corruption() {
        assert::fail("'U4V6'[93]", "out of bound");
        assert::fail("''[2]", "out of bound");
    }

    #[test]
    fn test_escape_characters() {
        // Test cases from the Starlark spec
        assert_eq!(
            assert::pass(r#"'\a\b\f\n\r\t\v'"#).to_string(),
            "\x07\x08\x0C\x0A\x0D\x09\x0B"
        );
        assert_eq!(assert::pass(r#"'\0'"#).to_string(), "\x00");
        assert_eq!(assert::pass(r#"'\12'"#).to_string(), "\n");
        assert_eq!(assert::pass(r#"'\101-\132'"#).to_string(), "A-Z");
        // 9 is not an octal digit, so it terminates early
        assert_eq!(assert::pass(r#"'\119'"#).to_string(), "\t9");
        assert_eq!(assert::pass(r#"'\117'"#).to_string(), "O");
        assert_eq!(assert::pass(r#"'\u0041'"#).to_string(), "A");
        assert_eq!(assert::pass(r#"'\u0414'"#).to_string(), "Д");
        assert_eq!(assert::pass(r#"'\u754c'"#).to_string(), "界");
        assert_eq!(assert::pass(r#"'\U0001F600'"#).to_string(), "😀");
    }

    const EXAMPLES: &[&str] = &[
        "",
        "short",
        "longer string which is all ASCII!#",
        "🤗",
        "mix of prefix ASCII and 🤗 some emjoi",
        "🤗 and the emjoi can go first",
        "😥🍊🍉🫐🥥🥬🥒🥑🍈🍋",
        "© and other characters Ŕ",
        "ça va bien merci",
        "Диана is a name in Russia",
    ];

    #[test]
    fn test_string_hash() {
        let heap = Heap::new();
        for x in EXAMPLES {
            assert_eq!(
                heap.alloc_str_hashed(x).hash(),
                heap.alloc(*x).get_hashed().unwrap().hash()
            );
        }
    }

    // If hash was zero, we'd need to mask the value in the hash cache.
    #[test]
    fn test_zero_length_string_hash_is_not_zero() {
        let heap = Heap::new();
        assert_ne!(0, heap.alloc("").get_hash().unwrap());
    }

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
    fn test_string_len() {
        assert::all_true(
            r#"
len("😿") == 1
"#,
        );
    }

    #[test]
    fn test_arithmetic_on_string() {
        assert::all_true(
            r#"
"abc" + "def" == "abcdef"
"abc" * 3 == "abcabcabc"
"#,
        );
    }

    #[test]
    fn test_slice_string() {
        let heap = Heap::new();
        for example in EXAMPLES {
            let s = heap.alloc_str(example);
            for i in -5..6 {
                for j in -5..6 {
                    let start = if i == 6 {
                        None
                    } else {
                        Some(Value::new_int(i))
                    };
                    let stop = if j == 6 {
                        None
                    } else {
                        Some(Value::new_int(j))
                    };
                    // Compare list slicing (comparatively simple) to string slicing (complex unicode)
                    let res1 = apply_slice(&example.chars().collect::<Vec<_>>(), start, stop, None)
                        .unwrap()
                        .iter()
                        .collect::<String>();
                    let res2 = s
                        .slice(start, stop, None, &heap)
                        .unwrap()
                        .unpack_str()
                        .unwrap();
                    assert_eq!(&res1, res2);
                }
            }
        }

        assert::all_true(
            r#"
"abc"[1:] == "bc" # Remove the first element
"abc"[:-1] == "ab" # Remove the last element
"abc"[1:-1] == "b" # Remove the first and the last element
"banana"[1::2] == "aaa" # Select one element out of 2, skipping the first
"banana"[4::-2] == "nnb" # Select one element out of 2 in reverse order, starting at index 4
"#,
        );
    }

    #[test]
    fn test_string_is_in() {
        assert::all_true(
            r#"
("a" in "abc") == True
("b" in "abc") == True
("bc" in "abc") == True
("bd" in "abc") == False
("z" in "abc") == False
"#,
        );
    }

    #[test]
    fn test_successive_add() {
        // we hope these get optimised away with adjacent plus optimisation
        assert::eq("x = 'c'\n'a' + 'b' + x + 'd' + 'e'", "'abcde'");
    }

    #[test]
    fn test_string_index() -> anyhow::Result<()> {
        fn test_str(str: &str) -> anyhow::Result<()> {
            let chars = str.chars().collect::<Vec<char>>();
            let heap = Heap::new();
            let val = heap.alloc(str);
            let len = chars.len() as i32;
            assert_eq!(val.length()?, len);
            for (i, char) in chars.iter().enumerate() {
                let char_str = char.to_string();
                assert_eq!(
                    val.at(Value::new_int(i as i32), &heap)?.unpack_str(),
                    Some(char_str.as_str())
                );
                assert_eq!(
                    val.at(Value::new_int(-len + (i as i32)), &heap)?
                        .unpack_str(),
                    Some(char_str.as_str())
                );
            }
            assert!(val.at(Value::new_int(len), &heap).is_err());
            assert!(val.at(Value::new_int(-(len + 1)), &heap).is_err());
            Ok(())
        }

        for x in EXAMPLES {
            // We use all trailing substrings of the test, for better coverage (especially around smart prefix algorithms)
            let mut it = x.chars();
            loop {
                test_str(it.as_str())?;
                if it.next().is_none() {
                    break;
                }
            }
        }
        Ok(())
    }
}
