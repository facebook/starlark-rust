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

use std::{iter, mem};

use crate::{
    codemap::CodeMap,
    eval::runtime::call_stack::FrozenFileSpan,
    values::{FrozenHeap, FrozenRef},
};

pub(crate) fn make_rust_source_span(
    file: &str,
    line: u32,
    col: u32,
) -> FrozenRef<'static, FrozenFileSpan> {
    let mut new_src = String::new();
    // Cheap way to make correct line and column number without adding offset support to `CodeMap`.
    // Technically, line (and column) number can be incorrect
    // if macro argument is after newline, but that is fine:
    // * line number will be approximately correct
    // * snippet will be correct
    // * file name will be correct
    new_src.extend(iter::repeat('\n').take(line as usize).skip(1));
    new_src.extend(iter::repeat(' ').take(col as usize).skip(1));
    let start_offset = new_src.len();
    new_src.push_str("<native>");

    let span = Span::new(
        Pos::new(start_offset as u32),
        Pos::new(new_src.len() as u32),
    );

    let heap = FrozenHeap::new();
    let codemap = CodeMap::new(file.to_owned(), new_src);
    let codemap = heap.alloc_any_display_from_debug(codemap);
    let file_span = heap.alloc_any(FrozenFileSpan {
        file: codemap,
        span,
    });
    mem::forget(heap);
    file_span
}

/// Initialize `$loc` to `FrozenRef<FrozenFileSpan>` with rust file and line number.
macro_rules! rust_loc {
    () => {{
        use once_cell::sync::Lazy;

        use crate::{
            eval::runtime::{call_stack::FrozenFileSpan, rust_loc::make_rust_source_span},
            values::FrozenRef,
        };
        static LOC: Lazy<FrozenRef<FrozenFileSpan>> =
            Lazy::new(|| make_rust_source_span(file!(), line!(), column!()));
        let loc: FrozenRef<FrozenFileSpan> = *LOC;
        loc
    }};
}

pub(crate) use rust_loc;

use crate::codemap::{Pos, Span};

#[cfg(test)]
mod tests {
    use crate as starlark;
    use crate::{assert::Assert, environment::GlobalsBuilder, eval::Arguments, values::Value};

    #[starlark_module]
    fn rust_loc_globals(globals: &mut GlobalsBuilder) {
        fn invoke<'v>(f: Value<'v>) -> anyhow::Result<Value<'v>> {
            f.invoke_with_loc(Some(rust_loc!()), &Arguments::default(), eval)
        }
    }

    #[test]
    fn test_rust_loc() {
        let mut a = Assert::new();
        a.globals_add(rust_loc_globals);
        let err = a.fail("invoke(fail)", "");
        let err = err.to_string();
        // Stack trace should contain invocation in `invoke`.
        assert!(
            // Make test compatible with Windows.
            err.replace('\\', "/")
                .contains("starlark/src/eval/runtime/rust_loc.rs"),
            "output: {:?}",
            err
        );
        assert!(err.contains("<native>"), "output: {:?}", err);
    }
}
