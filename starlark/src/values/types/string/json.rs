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

//! JSON escaping of strings.

pub(crate) fn json_escape(x: &str, collector: &mut String) {
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
