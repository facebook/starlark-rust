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

//! Implementation of `struct` function.

use crate::{
    collections::SmallMap,
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::{compare_small_map, equals_small_map},
        error::ValueError,
        unsupported_with, AllocValue, Freezer, Heap, ImmutableValue, MutableValue, TypedValue,
        Value, ValueLike, Walker,
    },
};
use gazebo::any::AnyLifetime;
use std::{
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

/// `struct()` implementation.

impl<T> StructGen<T> {
    pub const TYPE: &'static str = "struct";

    pub fn new(fields: SmallMap<String, T>) -> Self {
        Self { fields }
    }
}

starlark_value!(pub Struct);

#[derive(Clone, Default, Debug)]
pub struct StructGen<T> {
    pub fields: SmallMap<String, T>,
}

pub struct StructBuilder<'v>(&'v Heap, SmallMap<String, Value<'v>>);

impl<'v> StructBuilder<'v> {
    pub fn with_capacity(heap: &'v Heap, capacity: usize) -> Self {
        Self(heap, SmallMap::with_capacity(capacity))
    }

    pub fn new(heap: &'v Heap) -> Self {
        Self(heap, SmallMap::new())
    }

    pub fn add(&mut self, key: impl Into<String>, val: impl AllocValue<'v>) {
        self.1.insert(key.into(), self.0.alloc(val));
    }

    pub fn build(self) -> Struct<'v> {
        Struct { fields: self.1 }
    }
}

impl<'v> MutableValue<'v> for Struct<'v> {
    fn freeze<'fv>(self: Box<Self>, freezer: &'fv Freezer) -> Box<dyn ImmutableValue<'fv> + 'fv> {
        let mut frozen = SmallMap::with_capacity(self.fields.len());

        for (k, v) in self.fields.into_iter_hashed() {
            frozen.insert_hashed(k, v.freeze(freezer));
        }
        box FrozenStruct { fields: frozen }
    }

    fn walk(&mut self, walker: &Walker<'v>) {
        self.fields.values_mut().for_each(|v| walker.walk(v))
    }
}

impl<'v> ImmutableValue<'v> for FrozenStruct {}

impl<'v, T: ValueLike<'v>> TypedValue<'v> for StructGen<T>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(Struct::TYPE);

    fn get_members(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.members(crate::stdlib::structs::struct_members)
    }

    fn to_json(&self) -> String {
        let mut s = "{".to_string();
        s += &self
            .fields
            .iter()
            .map(|(k, v)| format!("\"{}\":{}", k, v.to_json()))
            .collect::<Vec<String>>()
            .join(",");
        s += "}";
        s
    }

    fn collect_repr(&self, r: &mut String) {
        r.push_str("struct(");
        for (i, (name, value)) in self.fields.iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            r.push_str(name);
            r.push('=');
            value.collect_repr(r);
        }
        r.push(')');
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match Struct::from_value(other) {
            None => Ok(false),
            Some(other) => equals_small_map(&self.fields, &other.fields, |x, y| x.equals(*y)),
        }
    }

    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        match Struct::from_value(other) {
            None => unsupported_with(self, "cmp()", other),
            Some(other) => compare_small_map(&self.fields, &other.fields, |x, y| x.compare(*y)),
        }
    }

    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match self.fields.get(attribute) {
            Some(v) => Ok(v.to_value()),
            None => Err(ValueError::OperationNotSupported {
                op: attribute.to_owned(),
                typ: self.to_repr(),
            }
            .into()),
        }
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        for (k, v) in self.fields.iter() {
            k.hash(&mut s);
            s.write_u64(v.get_hash()?);
        }
        Ok(s.finish())
    }

    fn has_attr(&self, attribute: &str) -> bool {
        self.fields.contains_key(attribute)
    }

    fn dir_attr(&self) -> Vec<String> {
        self.fields.keys().cloned().collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_to_json() {
        assert::eq("struct(key = None).to_json()", r#"'{"key":null}'"#);
        assert::eq("struct(key = True).to_json()", r#"'{"key":true}'"#);
        assert::eq("struct(key = False).to_json()", r#"'{"key":false}'"#);
        assert::eq("struct(key = 42).to_json()", r#"'{"key":42}'"#);
        assert::eq("struct(key = 'value').to_json()", r#"'{"key":"value"}'"#);
        assert::eq(
            r#"struct(key = 'value"').to_json()"#,
            r#"'{"key":"value\\\""}'"#,
        );
        assert::eq(
            r"struct(key = 'value\\').to_json()",
            r#"'{"key":"value\\\\"}'"#,
        );
        assert::eq(
            "struct(key = 'value/').to_json()",
            r#"'{"key":"value\\/"}'"#,
        );
        assert::eq(
            "struct(key = 'value\u{0008}').to_json()",
            r#"'{"key":"value\\b"}'"#,
        );
        assert::eq(
            "struct(key = 'value\u{000C}').to_json()",
            r#"'{"key":"value\\f"}'"#,
        );
        assert::eq(
            "struct(key = 'value\\n').to_json()",
            r#"'{"key":"value\\n"}'"#,
        );
        assert::eq(
            "struct(key = 'value\\r').to_json()",
            r#"'{"key":"value\\r"}'"#,
        );
        assert::eq(
            "struct(key = 'value\\t').to_json()",
            r#"'{"key":"value\\t"}'"#,
        );
        assert::eq(
            r#"struct(foo = 42, bar = "some").to_json()"#,
            r#"'{"foo":42,"bar":"some"}'"#,
        );
        assert::eq(
            r#"struct(foo = struct(bar = "some")).to_json()"#,
            r#"'{"foo":{"bar":"some"}}'"#,
        );
        assert::eq(
            r#"struct(foo = ["bar/", "some"]).to_json()"#,
            r#"'{"foo":["bar\\/","some"]}'"#,
        );
        assert::eq(
            r#"struct(foo = [struct(bar = "some")]).to_json()"#,
            r#"'{"foo":[{"bar":"some"}]}'"#,
        );
    }
}
