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

//! Define the string type for Starlark.
use crate::{
    environment::{Globals, GlobalsStatic},
    values::{
        fast_string, index::convert_slice_indices, interpolation::Interpolation, AllocFrozenValue,
        AllocValue, FrozenHeap, FrozenValue, Heap, StarlarkValue, Value, ValueError,
    },
};
use std::{
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

// We'd love to put this on a type, but we use String directly
pub const STRING_VALUE_TYPE_NAME: &str = "string";

impl<'v> AllocValue<'v> for String {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(self.into_boxed_str())
    }
}

impl<'v> AllocValue<'v> for char {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(self.to_string().into_boxed_str())
    }
}

impl<'v> AllocValue<'v> for &'_ String {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(Box::from(self.as_str()))
    }
}

impl<'v> AllocValue<'v> for &'_ str {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_str(Box::from(self))
    }
}

/// How to hash a string in a way that is compatible with Value
pub(crate) fn hash_string_value<H: Hasher>(x: &str, state: &mut H) {
    x.hash(state)
}

impl<'v> StarlarkValue<'v> for Box<str> {
    starlark_type!(STRING_VALUE_TYPE_NAME);

    fn get_members(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.members(crate::stdlib::string::string_members)
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
                    if x == 34 || x == 39 || x == 92 {
                        byte_buffer.push(92); // character for \
                    }
                    byte_buffer.push(x);
                }
            }
        }

        buffer.reserve(2 + self.len());
        buffer.push('"');
        loop_ascii(self, buffer);
        buffer.push('"');
    }

    fn to_json(&self) -> String {
        let mut escaped = self.as_ref().to_owned();
        // Escape as per ECMA-404 standard
        escaped = escaped.replace("\u{005C}", "\\\\");
        escaped = escaped.replace("\u{0022}", "\\\"");
        escaped = escaped.replace("\u{002F}", "\\/");
        escaped = escaped.replace("\u{0008}", "\\b");
        escaped = escaped.replace("\u{000C}", "\\f");
        escaped = escaped.replace("\u{000A}", "\\n");
        escaped = escaped.replace("\u{000D}", "\\r");
        escaped = escaped.replace("\u{0009}", "\\t");
        format!("\"{}\"", escaped)
    }

    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        hash_string_value(self.as_ref(), &mut s);
        Ok(s.finish())
    }

    fn equals(&self, other: Value) -> anyhow::Result<bool> {
        if let Some(other) = other.unpack_str() {
            Ok(*self.as_ref() == *other)
        } else {
            Ok(false)
        }
    }

    fn compare(&self, other: Value) -> anyhow::Result<Ordering> {
        if let Some(other) = other.unpack_str() {
            Ok(self.as_ref().cmp(other))
        } else {
            ValueError::unsupported_with(self, "cmp()", other)
        }
    }

    fn at(&self, index: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        // This method is disturbingly hot. Use the logic from `convert_index`,
        // but modified to be UTF8 string friendly.
        match index.to_int() {
            Err(_) => Err(ValueError::IncorrectParameterType.into()),
            Ok(i) => {
                if i >= 0 {
                    match fast_string::at(self, i as usize) {
                        None => Err(ValueError::IndexOutOfBound(i).into()),
                        Some(c) => Ok(heap.alloc(c.to_string())),
                    }
                } else {
                    let len = fast_string::len(self);
                    let ind = (-i) as usize; // Index from the end, minimum of 1
                    if ind > len {
                        Err(ValueError::IndexOutOfBound(i).into())
                    } else if len == self.len() {
                        // We are a 7bit ASCII string, so take the fast-path
                        Ok(heap.alloc(self.as_bytes()[len - ind] as char))
                    } else {
                        Ok(heap.alloc(fast_string::at(self, len - ind).unwrap()))
                    }
                }
            }
        }
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(fast_string::len(self) as i32)
    }

    fn is_in(&self, other: Value) -> anyhow::Result<bool> {
        match other.unpack_str() {
            Some(s) => Ok(self.contains(s)),
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
        let (start, stop, stride) = convert_slice_indices(self.len() as i32, start, stop, stride)?;
        let (low, take, astride) = if stride < 0 {
            (stop + 1, start - stop, -stride)
        } else {
            (start, stop - start, stride)
        };
        if take <= 0 {
            return Ok(heap.alloc(""));
        };

        let v: String = self
            .chars()
            .skip(low as usize)
            .take(take as usize)
            .collect();
        let v: String = if stride > 0 {
            v.chars()
                .enumerate()
                .filter_map(|x| {
                    if 0 == (x.0 as i32 % astride) {
                        Some(x.1)
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            v.chars()
                .rev()
                .enumerate()
                .filter_map(|x| {
                    if 0 == (x.0 as i32 % astride) {
                        Some(x.1)
                    } else {
                        None
                    }
                })
                .collect()
        };
        Ok(heap.alloc(v))
    }

    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other_str) = other.unpack_str() {
            if self.is_empty() {
                Ok(other)
            } else {
                Ok(heap.alloc(fast_string::append(self, other_str)))
            }
        } else {
            ValueError::unsupported_with(self, "+", other)
        }
    }

    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_int() {
            Some(l) => {
                let mut result = String::new();
                for _i in 0..l {
                    result += self
                }
                Ok(heap.alloc(result))
            }
            None => Err(ValueError::IncorrectParameterType.into()),
        }
    }

    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        Ok(heap.alloc(Interpolation::parse(self)?.apply(other, heap)?))
    }
}

impl AllocFrozenValue for String {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_str(self.into_boxed_str())
    }
}

impl<'v, 'a> AllocFrozenValue for &'a str {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_str(Box::from(self))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        assert,
        values::{Heap, Value},
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

        let examples = &[
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
            "🤗 and the emjoi can go first",
            "😥🍊🍉🫐🥥🥬🥒🥑🍈🍋",
        ];

        for x in examples {
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
