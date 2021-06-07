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

use crate::{
    self as starlark,
    environment::GlobalsBuilder,
    values::{none::NoneType, Value},
};

#[starlark_module]
pub fn global(builder: &mut GlobalsBuilder) {
    fn assert_type(ref v: Value, ref ty: Value) -> NoneType {
        v.check_type(ty, Some("v"))?;
        Ok(NoneType)
    }

    fn is_type(ref v: Value, ref ty: Value) -> bool {
        v.is_type(ty)
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_types() {
        let a = assert::Assert::new();
        a.is_true(
            r#"
def f(i: int.type) -> bool.type:
    return i == 3
f(8) == False"#,
        );

        // If the types are either malformed or runtime errors, it should fail
        a.fail("def f(i: made_up):\n pass", "Variable");
        a.fail("def f(i: fail('bad')):\n pass", "bad");

        // Type errors should be caught in arguments
        a.fails(
            "def f(i: bool.type):\n pass\nf(1)",
            &["type annotation", "`1`", "`int`", "`bool`", "`i`"],
        );
        // Type errors should be caught in return positions
        a.fails(
            "def f() -> bool.type:\n return 1\nf()",
            &["type annotation", "`1`", "`bool`", "`int`", "return"],
        );
        // And for functions without return
        a.fails(
            "def f() -> bool.type:\n pass\nf()",
            &["type annotation", "`None`", "`bool`", "return"],
        );
        // And for functions that return None implicitly or explicitly
        a.fails(
            "def f() -> None:\n return True\nf()",
            &["type annotation", "`None`", "`bool`", "return"],
        );
        a.pass("def f() -> None:\n pass\nf()");

        // The following are all valid types
        a.all_true(
            r#"
is_type(1, int.type)
is_type(True, bool.type)
is_type(True, "")
is_type(None, None)
is_type(assert_type, "function")
is_type([], [int.type])
is_type([], [""])
is_type([1, 2, 3], [int.type])
is_type(None, [None, int.type])
is_type('test', [int.type, str.type])
is_type(('test', None), (str.type, None))
is_type({1: 'test', 2: False, 3: 3}, {1: str.type, 2: bool.type})
is_type({"test": 1, "more": 2}, {str.type: int.type})
is_type({1: 1, 2: 2}, {int.type: int.type})

not is_type(1, None)
not is_type((1, 1), str.type)
not is_type({1: 'test', 3: 'test'}, {2: bool.type, 3: str.type})
not is_type({1: 'test', 3: 'test'}, {1: bool.type, 3: str.type})
not is_type('test', [int.type, bool.type])
not is_type([1,2,None], [int.type])
not is_type({"test": 1, 8: 2}, {str.type: int.type})
not is_type({"test": 1, "more": None}, {str.type: int.type})

is_type(1, "")
is_type([1,2,"test"], ["_a"])
"#,
        );

        // Checking types fails for invalid types
        a.fail("is_type(None, is_type)", "not a valid type");
        a.fail("is_type(None, [])", "not a valid type");
    }
}
