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

//! The struct type, an associative-map created with `struct()`.
//!
//! This struct type is related to both the [dictionary](crate::values::dict) and the
//! [record](crate::values::record) types, all being associative maps.
//!
//! * Like a record, a struct is immutable, fields can be referred to with `struct.field`, and
//!   it uses strings for keys.
//! * Like a dictionary, the struct is untyped, and manipulating structs from Rust is ergonomic.
//!
//! The `struct()` function creates a struct. It accepts keyword arguments, keys become
//! struct field names, and values become field values.
//!
//! ```
//! # starlark::assert::is_true(r#"
//! ip_address = struct(host='localhost', port=80)
//! ip_address.port == 80
//! # "#);
//! ```

use crate as starlark;
use crate::{
    collections::SmallMap,
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::{compare_small_map, equals_small_map},
        dict::ValueStr,
        error::ValueError,
        AllocValue, ComplexValue, Freezer, Heap, StarlarkValue, Trace, Value, ValueLike,
    },
};
use gazebo::{
    any::AnyLifetime,
    coerce::{coerce_ref, Coerce},
};
use std::{
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

impl<V> StructGen<V> {
    /// The result of calling `type()` on a struct.
    pub const TYPE: &'static str = "struct";

    /// Create a new [`Struct`].
    pub fn new(fields: SmallMap<V, V>) -> Self {
        Self { fields }
    }
}

starlark_complex_value!(pub Struct);

/// The result of calling `struct()`.
#[derive(Clone, Default, Debug, Trace, Coerce)]
#[repr(transparent)]
pub struct StructGen<V> {
    /// The fields in a struct.
    /// All keys _must_ be strings.
    pub fields: SmallMap<V, V>,
}

/// A builder to create a `Struct` easily.
pub struct StructBuilder<'v>(&'v Heap, SmallMap<Value<'v>, Value<'v>>);

impl<'v> StructBuilder<'v> {
    /// Create a new [`StructBuilder`] with a given capacity.
    pub fn with_capacity(heap: &'v Heap, capacity: usize) -> Self {
        Self(heap, SmallMap::with_capacity(capacity))
    }

    /// Create a new [`StructBuilder`].
    pub fn new(heap: &'v Heap) -> Self {
        Self(heap, SmallMap::new())
    }

    /// Add an element to the underlying [`Struct`].
    pub fn add(&mut self, key: &str, val: impl AllocValue<'v>) {
        self.1
            .insert_hashed(self.0.alloc_str_hashed(key), self.0.alloc(val));
    }

    /// Finish building and produce a [`Struct`].
    pub fn build(self) -> Struct<'v> {
        Struct { fields: self.1 }
    }
}

impl<'v> ComplexValue<'v> for Struct<'v> {
    type Frozen = FrozenStruct;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        let mut frozen = SmallMap::with_capacity(self.fields.len());
        for (k, v) in self.fields.into_iter_hashed() {
            frozen.insert_hashed(k.freeze(freezer)?, v.freeze(freezer)?);
        }
        Ok(FrozenStruct { fields: frozen })
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for StructGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(Struct::TYPE);

    fn get_methods(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.methods(crate::stdlib::structs::struct_methods)
    }

    fn extra_memory(&self) -> usize {
        self.fields.extra_memory()
    }

    fn to_json(&self) -> anyhow::Result<String> {
        let mut s = "{".to_owned();
        s += &self
            .fields
            .iter()
            .map(|(k, v)| {
                Ok(format!(
                    "\"{}\":{}",
                    k.to_value().unpack_str().unwrap(),
                    v.to_json()?
                ))
            })
            .collect::<anyhow::Result<Vec<String>>>()?
            .join(",");
        s += "}";
        Ok(s)
    }

    fn collect_repr(&self, r: &mut String) {
        r.push_str("struct(");
        for (i, (name, value)) in self.fields.iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            r.push_str(name.to_value().unpack_str().unwrap());
            r.push('=');
            value.collect_repr(r);
        }
        r.push(')');
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match Struct::from_value(other) {
            None => Ok(false),
            Some(other) => {
                equals_small_map(coerce_ref(&self.fields), &other.fields, |x, y| x.equals(*y))
            }
        }
    }

    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        match Struct::from_value(other) {
            None => ValueError::unsupported_with(self, "cmp()", other),
            Some(other) => compare_small_map(
                coerce_ref(&self.fields),
                &other.fields,
                |k| k.unpack_str(),
                |x, y| x.compare(*y),
            ),
        }
    }

    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> Option<Value<'v>> {
        coerce_ref(&self.fields).get(&ValueStr(attribute)).copied()
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        for (k, v) in self.fields.iter_hashed() {
            Hash::hash(&k, &mut s);
            s.write_u64(v.get_hash()?);
        }
        Ok(s.finish())
    }

    fn has_attr(&self, attribute: &str) -> bool {
        coerce_ref(&self.fields).contains_key(&ValueStr(attribute))
    }

    fn dir_attr(&self) -> Vec<String> {
        self.fields
            .keys()
            .map(|x| x.to_value().unpack_str().unwrap().to_owned())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_to_json() {
        assert::pass(
            r#"
struct(key = None).to_json() == '{"key":null}'
struct(key = True).to_json() == '{"key":true}'
struct(key = False).to_json() == '{"key":false}'
struct(key = 42).to_json() == '{"key":42}'
struct(key = 'value').to_json() == '{"key":"value"}'
struct(key = 'value"').to_json() == '{"key":"value\\\""}'
struct(key = 'value\\').to_json() == '{"key":"value\\\\"}'
struct(key = 'value/').to_json() == '{"key":"value/"}'
struct(key = 'value\u0008').to_json() == '{"key":"value\\b"}'
struct(key = 'value\u000C').to_json() == '{"key":"value\\f"}'
struct(key = 'value\\n').to_json() == '{"key":"value\\n"}'
struct(key = 'value\\r').to_json() == '{"key":"value\\r"}'
struct(key = 'value\\t').to_json() == '{"key":"value\\t"}'
struct(foo = 42, bar = "some").to_json() == '{"foo":42,"bar":"some"}'
struct(foo = struct(bar = "some")).to_json() == '{"foo":{"bar":"some"}}'
struct(foo = ["bar/", "some"]).to_json() == '{"foo":["bar/","some"]}'
struct(foo = [struct(bar = "some")]).to_json() == '{"foo":[{"bar":"some"}]}'
"#,
        );
    }
}
