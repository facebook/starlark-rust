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

//! Implementation of `record` function.
use crate as starlark;
use crate::{
    collections::SmallMap,
    environment::GlobalsBuilder,
    values::{
        record::{Field, RecordType},
        Value,
    },
};
use gazebo::prelude::*;

#[starlark_module]
pub fn global(builder: &mut GlobalsBuilder) {
    /// Creates a record.
    ///
    /// `record` creates a record type. It accepts keyword arguments, keys become
    /// struct field names, and values are the types. Calling the resulting
    /// function produces an actual record.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::is_true(r#"
    /// rec_type = record(host=String, port=Int)
    /// rec = rec_type(host="localhost", port=80)
    /// rec.port == 80
    /// # "#);
    /// ```
    fn record(kwargs: SmallMap<String, Value>) -> RecordType<'v> {
        // Every Value must either be a field or a value (the type)
        let mut mp = SmallMap::with_capacity(kwargs.len());
        for (k, v) in kwargs.into_iter_hashed() {
            let field = match Field::from_value(v) {
                None => Field::new(v, None),
                Some(v) => v.dupe(),
            };
            mp.insert_hashed(k, field);
        }
        Ok(RecordType::new(mp))
    }

    /// Creates a field record.
    ///
    /// Examples:
    ///
    /// ```
    /// # starlark::assert::is_true(r#"
    /// rec_type = record(host=field(String), port=field(type=Int), mask=field(Int, default=255))
    /// rec = rec_type(host="localhost", port=80)
    /// rec.port == 80
    /// rec.mask == 255
    /// # "#);
    /// ```
    fn field(_type: Value, default: Option<Value>) -> Field<'v> {
        Ok(Field::new(_type, default))
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_record() {
        assert::pass(
            r#"
rec_type = record(host=String, port=Int)
rec1 = rec_type(host = "test", port=80)
rec2 = rec_type(host = "test", port=90)
assert_eq(rec1, rec1)
assert_eq(rec1 == rec2, False)
"#,
        );
        assert::fails(
            r#"
rec_type = record(host=String, port=Int)
rec_type(host=1, port=80)
"#,
            &["`1`", "`string`", "`host`"],
        );
        assert::fails(
            r#"
rec_type = record(host=String, port=Int)
rec_type(port=80)
"#,
            &["Missing parameter", "`host`"],
        );
        assert::fails(
            r#"
rec_type = record(host=String, port=Int)
rec_type(host="localhost", port=80, mask=255)
"#,
            &["extra named", "mask"],
        );
        assert::pass(
            r#"
rec_type = record(host=String, port=Int)
def foo(x: rec_type.type) -> "rec_type":
    return x
foo(rec_type(host="localhost", port=80))"#,
        );
        assert::pass(
            r#"
v = [record(host=String, port=Int)]
def foo(x: v[0].type) -> "record":
    return x
foo(v[0](host="localhost", port=80))"#,
        );
        assert::pass(
            r#"
rec_type = record(host=String, port=field(Int, 80), mask=Int)
assert_eq(rec_type(host="localhost", mask=255), rec_type(host="localhost", port=80, mask=255))"#,
        );
    }
}
