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
    values::{
        bool::BOOL_VALUE_TYPE_NAME, dict::Dict, function::FUNCTION_VALUE_TYPE_NAME,
        int::INT_VALUE_TYPE_NAME, list::List, none::NoneType, range::Range,
        string::STRING_VALUE_TYPE_NAME, structs::Struct, tuple::Tuple, Value,
    },
};

#[starlark_module]
pub fn global(builder: &mut GlobalsBuilder) {
    const Any: &str = "";
    const Void: &str = "void";
    const Bool: &str = BOOL_VALUE_TYPE_NAME;
    const Int: &str = INT_VALUE_TYPE_NAME;
    const String: &str = STRING_VALUE_TYPE_NAME;
    const Function: &str = FUNCTION_VALUE_TYPE_NAME;
    const List: &str = List::TYPE;
    const Tuple: &str = Tuple::TYPE;
    const Dict: &str = Dict::TYPE;
    const Struct: &str = Struct::TYPE;
    const Range: &str = Range::TYPE;

    #[allow(non_snake_case)]
    fn Union(args: Vec<Value>) -> Value<'v> {
        match args.len() {
            0 => Ok(heap.alloc("void")),
            1 => Ok(args[0]),
            _ => Ok(heap.alloc(args)),
        }
    }

    #[allow(non_snake_case)]
    fn Nullable(x: Value) -> Vec<Value<'v>> {
        Ok(vec![x, Value::new_none()])
    }

    fn assert_type(v: Value, ty: Value) -> NoneType {
        v.check_type(ty, Some("v"))?;
        Ok(NoneType)
    }

    fn is_type(v: Value, ty: Value) -> bool {
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
def f(i: Int) -> Bool:
    return i == 3
f(8) == False"#,
        );

        // If the types are either malformed or runtime errors, it should fail
        a.fail("def f(i: made_up):\n pass", "Variable");
        a.fail("def f(i: fail('bad')):\n pass", "bad");

        // Type errors should be caught in arguments
        a.fails(
            "def f(i: Bool):\n pass\nf(1)",
            &["type annotation", "`1`", "`int`", "`bool`", "`i`"],
        );
        // Type errors should be caught in return positions
        a.fails(
            "def f() -> Bool:\n return 1\nf()",
            &["type annotation", "`1`", "`bool`", "`int`", "return"],
        );
        // And for functions without return
        a.fails(
            "def f() -> Bool:\n pass\nf()",
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
is_type(1, Int)
is_type(True, Bool)
is_type(True, Any)
is_type(None, None)
is_type(assert_type, Function)
is_type([], [Int])
is_type([], [Any])
is_type([1, 2, 3], [Int])
is_type(None, Nullable(Int))
is_type('test', Union(Int, String))
is_type(('test', None), (String, None))
is_type({1: 'test'}, {1: String})
is_type({1: 'test', 2: False}, {1: String})
is_type({"test": 1, "more": 2}, {"": Int})

not is_type(1, None)
not is_type((1, 1), String)
not is_type({1: 'test'}, {2: Bool})
not is_type({1: 'test'}, {1: Bool})
not is_type('test', Union(Int, Bool))
not is_type([1,2,None], [Int])
not is_type({"test": 1, 8: 2}, {"": Int})
not is_type({"test": 1, "more": None}, {"": Int})

is_type(1, "_")
is_type([1,2,"test"], ["_a"])
"#,
        );

        // Checking types fails for invalid types
        a.fail("is_type(None, is_type)", "not a valid type");
        a.fail("is_type(None, [])", "not a valid type");
    }
}
