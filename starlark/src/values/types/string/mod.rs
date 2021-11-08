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

use std::{
    cmp,
    cmp::Ordering,
    fmt,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
    slice, str,
    sync::atomic,
};

use derive_more::Display;
use gazebo::{any::AnyLifetime, coerce::Coerce, prelude::OptionExt};

use crate as starlark;
use crate::{
    collections::{BorrowHashed, SmallHashResult, StarlarkHasher},
    environment::{Methods, MethodsStatic},
    values::{
        index::apply_slice, string::repr::string_repr, AllocFrozenValue, AllocValue, Freeze,
        FrozenHeap, FrozenValue, Heap, StarlarkValue, Trace, UnpackValue, Value, ValueError,
        ValueLike,
    },
};

pub(crate) mod fast_string;
pub(crate) mod interpolation;
mod repr;
pub(crate) mod simd;

/// The result of calling `type()` on strings.
pub const STRING_TYPE: &str = "string";

#[repr(C)] // We want the body to come after len
pub(crate) struct StarlarkStrN<const N: usize> {
    // Lazily-initialized cached hash code.
    pub(crate) hash: atomic::AtomicU32,
    // Length in bytes.
    pub(crate) len: u32,
    // Followed by an unsized block, meaning this type is unsized.
    // But we can't mark it as such since we really want &StarlarkStr to
    // take up only one word.
    pub(crate) body: [u8; N],
}

unsafe impl<'a, const N: usize> AnyLifetime<'a> for StarlarkStrN<N> {
    any_lifetime_body!(StarlarkStrN<N>);
}

/// A pointer to this type represents a Starlark string.
/// Use of this type is discouraged and not considered stable.
#[derive(AnyLifetime)]
#[repr(C)]
pub struct StarlarkStr {
    str: StarlarkStrN<0>,
}

impl Deref for StarlarkStr {
    type Target = str;

    fn deref(&self) -> &str {
        self.unpack()
    }
}

impl Debug for StarlarkStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.unpack(), f)
    }
}

impl StarlarkStr {
    /// Unsafe because if you do `unpack` on this it will blow up
    pub(crate) const unsafe fn new(len: usize) -> Self {
        assert!(len as u32 as usize == len, "len overflow");
        StarlarkStr {
            str: StarlarkStrN {
                hash: atomic::AtomicU32::new(0),
                len: len as u32,
                body: [],
            },
        }
    }

    pub fn unpack(&self) -> &str {
        unsafe {
            let slice = slice::from_raw_parts(self.str.body.as_ptr(), self.str.len as usize);
            str::from_utf8_unchecked(slice)
        }
    }

    pub(crate) fn get_small_hash_result(&self) -> SmallHashResult {
        // Note relaxed load and store are practically non-locking memory operations.
        let hash = self.str.hash.load(atomic::Ordering::Relaxed);
        if hash != 0 {
            SmallHashResult::new_unchecked(hash)
        } else {
            let mut s = StarlarkHasher::new();
            hash_string_value(self.unpack(), &mut s);
            let hash = s.finish_small();
            // If hash is zero, we are unlucky, but it is highly improbable.
            self.str.hash.store(hash.get(), atomic::Ordering::Relaxed);
            hash
        }
    }

    pub fn as_str_hashed(&self) -> BorrowHashed<str> {
        BorrowHashed::new_unchecked(self.get_small_hash_result(), self.unpack())
    }

    pub fn len(&self) -> usize {
        self.str.len as usize
    }

    pub fn is_empty(&self) -> bool {
        self.str.len == 0
    }

    pub fn offset_of_content() -> usize {
        memoffset::offset_of!(StarlarkStrN<0>, body)
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
    fn expected() -> String {
        "str".to_owned()
    }

    fn unpack_value(value: Value<'v>) -> Option<Self> {
        value.unpack_str()
    }
}

impl<'v> UnpackValue<'v> for String {
    fn expected() -> String {
        "str".to_owned()
    }

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

fn json_escape(x: &str, collector: &mut String) {
    collector.reserve(x.len() + 2);
    // Safe because we only put valid UTF8 into it
    let bytes = unsafe { collector.as_mut_vec() };
    bytes.push(b'\"');
    for c in x.bytes() {
        // Escape as per ECMA-404 standard
        match c {
            b'\\' => bytes.extend(b"\\\\".iter()),
            b'"' => bytes.extend(b"\\\"".iter()),
            0x08u8 => bytes.extend(b"\\b".iter()),
            0x0Cu8 => bytes.extend(b"\\f".iter()),
            b'\n' => bytes.extend(b"\\n".iter()),
            b'\r' => bytes.extend(b"\\r".iter()),
            b'\t' => bytes.extend(b"\\t".iter()),
            x => bytes.push(x),
        }
    }
    bytes.push(b'\"');
}

impl Display for StarlarkStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We could either accumulate straight into the buffer (can't preallocate, virtual call on each character)
        // or accumulate into a String buffer first. Not sure which is faster, but string buffer lets us
        // share code with collect_repr more easily.
        let mut buffer = String::new();
        string_repr(self.unpack(), &mut buffer);
        f.write_str(&buffer)
    }
}

// We don't actually use `str` on the heap, but it's helpful to have an instance
// for people who want to get access to repr/json "like string"
impl<'v> StarlarkValue<'v> for str {
    starlark_type!(STRING_TYPE);

    fn get_methods(&self) -> Option<&'static Methods> {
        static RES: MethodsStatic = MethodsStatic::new();
        RES.methods(crate::stdlib::string::string_methods)
    }

    fn collect_repr(&self, buffer: &mut String) {
        // String repr() is quite hot, so optimise it
        string_repr(self, buffer)
    }

    fn collect_json(&self, collector: &mut String) -> anyhow::Result<()> {
        json_escape(self, collector);
        Ok(())
    }

    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn write_hash(&self, hasher: &mut StarlarkHasher) -> anyhow::Result<()> {
        let mut s = StarlarkHasher::new();
        hash_string_value(self, &mut s);
        let hash = s.finish_small();
        hasher.write_u32(hash.get());
        Ok(())
    }

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        if let Some(other) = other.unpack_str() {
            Ok(self == other)
        } else {
            Ok(false)
        }
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        if let Some(other) = other.unpack_str() {
            Ok(self.cmp(other))
        } else {
            ValueError::unsupported_with(self, "cmp()", other)
        }
    }

    fn at(&self, index: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        // This method is disturbingly hot. Use the logic from `convert_index`,
        // but modified to be UTF8 string friendly.
        let i = i32::unpack_param(index)?;
        if i >= 0 {
            match fast_string::at(self, i as usize) {
                None => Err(ValueError::IndexOutOfBound(i).into()),
                Some(c) => Ok(heap.alloc(c)),
            }
        } else {
            let len_chars = fast_string::len(self);
            let ind = (-i) as usize; // Index from the end, minimum of 1
            if ind > len_chars {
                Err(ValueError::IndexOutOfBound(i).into())
            } else if len_chars == self.len() {
                // We are a 7bit ASCII string, so take the fast-path
                Ok(heap.alloc(self.as_bytes()[len_chars - ind] as char))
            } else {
                Ok(heap.alloc(fast_string::at(self, len_chars - ind).unwrap()))
            }
        }
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(fast_string::len(self) as i32)
    }

    fn is_in(&self, other: Value) -> anyhow::Result<bool> {
        let s = <&str>::unpack_param(other)?;
        if s.len() == 1 {
            Ok(self.as_bytes().contains(&s.as_bytes()[0]))
        } else {
            Ok(self.contains(s))
        }
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        let s = self;
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
                Ok(heap.alloc_str_concat(self, other_str))
            }
        } else {
            ValueError::unsupported_with(self, "+", other)
        }
    }

    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let l = i32::unpack_param(other)?;
        let mut result = String::with_capacity(self.len() * cmp::max(0, l) as usize);
        for _i in 0..l {
            result.push_str(self)
        }
        Ok(heap.alloc(result))
    }

    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(heap.alloc(interpolation::percent(self, other)?))
    }
}

impl<'v> StarlarkValue<'v> for StarlarkStr {
    starlark_type!(STRING_TYPE);

    fn write_hash(&self, hasher: &mut StarlarkHasher) -> anyhow::Result<()> {
        // Don't defer to str because we cache the Hash in StarlarkStr
        hasher.write_u32(self.get_small_hash_result().get());
        Ok(())
    }

    fn extra_memory(&self) -> usize {
        // We don't include the extra_memory for the size because it is
        // allocated inline in the Starlark heap (which knows about it),
        // not on the malloc heap.
        0
    }

    fn get_methods(&self) -> Option<&'static Methods> {
        self.unpack().get_methods()
    }

    fn collect_repr(&self, collector: &mut String) {
        self.unpack().collect_repr(collector)
    }

    fn collect_json(&self, collector: &mut String) -> anyhow::Result<()> {
        self.unpack().collect_json(collector)
    }

    fn to_bool(&self) -> bool {
        self.unpack().to_bool()
    }

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        self.unpack().equals(other)
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        self.unpack().compare(other)
    }

    fn at(&self, index: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.unpack().at(index, heap)
    }

    fn length(&self) -> anyhow::Result<i32> {
        self.unpack().length()
    }

    fn is_in(&self, other: Value) -> anyhow::Result<bool> {
        self.unpack().is_in(other)
    }

    fn slice(
        &self,
        start: Option<Value<'v>>,
        stop: Option<Value<'v>>,
        stride: Option<Value<'v>>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        self.unpack().slice(start, stop, stride, heap)
    }

    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.unpack().add(other, heap)
    }

    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.unpack().mul(other, heap)
    }

    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.unpack().percent(other, heap)
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
#[derive(Debug, Trace, Coerce, Display, Freeze)]
#[display(fmt = "iterator")]
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

#[cfg(test)]
mod tests {
    use crate::{
        assert,
        values::{index::apply_slice, Heap, Value},
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
            assert::pass(r#"'\a\b\f\n\r\t\v'"#).unpack_str().unwrap(),
            "\x07\x08\x0C\x0A\x0D\x09\x0B"
        );
        assert_eq!(assert::pass(r#"'\0'"#).unpack_str().unwrap(), "\x00");
        assert_eq!(assert::pass(r#"'\12'"#).unpack_str().unwrap(), "\n");
        assert_eq!(assert::pass(r#"'\101-\132'"#).unpack_str().unwrap(), "A-Z");
        // 9 is not an octal digit, so it terminates early
        assert_eq!(assert::pass(r#"'\119'"#).unpack_str().unwrap(), "\t9");
        assert_eq!(assert::pass(r#"'\117'"#).unpack_str().unwrap(), "O");
        assert_eq!(assert::pass(r#"'\u0041'"#).unpack_str().unwrap(), "A");
        assert_eq!(assert::pass(r#"'\u0414'"#).unpack_str().unwrap(), "Д");
        assert_eq!(assert::pass(r#"'\u754c'"#).unpack_str().unwrap(), "界");
        assert_eq!(assert::pass(r#"'\U0001F600'"#).unpack_str().unwrap(), "😀");
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
        assert_ne!(0, heap.alloc("").get_hash().unwrap().get());
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
"242"[ -0:-2:-1] == "" # From https://github.com/facebookexperimental/starlark-rust/issues/35
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
