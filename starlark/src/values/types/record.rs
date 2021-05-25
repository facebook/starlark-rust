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

//! A `record` type, comprising of a fixed set of fields.
//!
//! Calling `record()` produces a [`RecordType`]. Calling [`RecordType`] produces a [`Record`].
//! The field names of the record are only stored once, potentially reducing memory usage.
//! Created in Starlark using the `record()` function, which accepts keyword arguments.
//! The keys become field names, and values are the types. Calling the resulting
//! function produces an actual record.
//!
//! ```
//! # starlark::assert::is_true(r#"
//! IpAddress = record(host=str.type, port=int.type)
//! rec = IpAddress(host="localhost", port=80)
//! rec.port == 80
//! # "#);
//! ```
//!
//! It is also possible to use `field(type, default)` type to give defaults:
//!
//! ```
//! # starlark::assert::is_true(r#"
//! IpAddress = record(host=str.type, port=field(int.type, 80))
//! rec = IpAddress(host="localhost")
//! rec.port == 80
//! # "#);
//! ```

use crate::{
    collections::SmallMap,
    eval::{Evaluator, ParametersParser, ParametersSpec},
    values::{
        comparison::equals_slice,
        error::ValueError,
        function::{FunctionInvoker, NativeFunction, FUNCTION_TYPE},
        ComplexValue, Freezer, Heap, SimpleValue, StarlarkValue, Value, ValueLike, Walker,
    },
};
use gazebo::{any::AnyLifetime, cell::ARef, prelude::*};
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

/// The result of `field()`.
#[derive(Clone, Debug, Dupe)]
pub struct FieldGen<V> {
    typ: V,
    default: Option<V>,
}

/// The result of `record()`, being the type of records.
#[derive(Clone, Debug)]
pub struct RecordTypeGen<V> {
    /// The name of this type, e.g. MyRecord
    typ: Option<String>,
    /// The V is the type the field must satisfy (e.g. `"string"`)
    fields: SmallMap<String, FieldGen<V>>,
    /// The construction function, which takes a hidden parameter (this type)
    /// followed by the arguments of the field.
    /// Creating these on every invoke is pretty expensive (profiling shows)
    /// so compute them in advance and cache.
    constructor: V,
}

/// An actual record.
#[derive(Clone, Debug)]
pub struct RecordGen<V> {
    typ: V, // Must be RecordType
    values: Vec<V>,
}

starlark_complex_value!(pub(crate) Field);
starlark_complex_value!(pub RecordType);
starlark_complex_value!(pub Record);

impl<V> FieldGen<V> {
    pub(crate) fn new(typ: V, default: Option<V>) -> Self {
        Self { typ, default }
    }
}

impl<'v> Field<'v> {
    fn freeze(self, freezer: &Freezer) -> FrozenField {
        FrozenField {
            typ: self.typ.freeze(freezer),
            default: self.default.map(|x| x.freeze(freezer)),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        walker.walk(&mut self.typ);
        walker.walk_opt(&mut self.default);
    }
}

fn collect_repr_record<'s, 't, V: 't>(
    items: impl Iterator<Item = (&'s String, &'t V)>,
    add: impl Fn(&'t V, &mut String),
    collector: &mut String,
) {
    collector.push_str("record(");
    for (i, (name, typ)) in items.enumerate() {
        if i != 0 {
            collector.push_str(", ");
        }
        collector.push_str(name);
        collector.push('=');
        add(typ, collector);
    }
    collector.push(')');
}

impl<'v> RecordType<'v> {
    pub(crate) fn new(fields: SmallMap<String, FieldGen<Value<'v>>>, heap: &'v Heap) -> Self {
        let constructor = heap.alloc(Self::make_constructor(&fields));
        Self {
            typ: None,
            fields,
            constructor,
        }
    }

    fn make_constructor(fields: &SmallMap<String, FieldGen<Value<'v>>>) -> NativeFunction {
        let mut parameters = ParametersSpec::with_capacity("record".to_owned(), fields.len() + 1);
        parameters.required("me"); // Hidden first argument
        parameters.no_args();
        for (name, field) in fields {
            if field.default.is_some() {
                parameters.optional(name);
            } else {
                parameters.required(name);
            }
        }

        // We want to get the value of `me` into the function, but that doesn't work since it
        // might move between threads - so we create the NativeFunction and apply it later.
        NativeFunction::new(
            move |eval, mut param_parser: ParametersParser| {
                let me = param_parser.next("me", eval)?;
                let info = RecordType::from_value(me).unwrap();
                let mut values = Vec::with_capacity(info.fields.len());
                for (name, field) in &info.fields {
                    match field.default {
                        None => {
                            let v: Value = param_parser.next(name, eval)?;
                            v.check_type(field.typ, Some(name))?;
                            values.push(v);
                        }
                        Some(default) => {
                            let v: Option<Value> = param_parser.next_opt(name, eval)?;
                            match v {
                                None => values.push(default),
                                Some(v) => {
                                    v.check_type(field.typ, Some(name))?;
                                    values.push(v);
                                }
                            }
                        }
                    }
                }
                Ok(eval.heap().alloc_complex(Record { typ: me, values }))
            },
            parameters,
        )
    }
}

impl<'v, V: ValueLike<'v>> RecordGen<V> {
    pub const TYPE: &'static str = "record";

    fn get_record_type(&self) -> ARef<'v, RecordType<'v>> {
        // Safe to unwrap because we always ensure typ is RecordType
        RecordType::from_value(self.typ.to_value()).unwrap()
    }
}

impl<'v> ComplexValue<'v> for Field<'v> {
    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        box (*self).freeze(freezer)
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        self.walk(walker)
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for FieldGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!("field");

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str("field(");
        self.typ.collect_repr(collector);
        if let Some(d) = self.default {
            collector.push_str(", ");
            d.collect_repr(collector);
        }
        collector.push(')');
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        s.write_u64(self.typ.get_hash()?);
        self.default.is_some().hash(&mut s);
        if let Some(d) = self.default {
            s.write_u64(d.get_hash()?);
        }
        Ok(s.finish())
    }
}

impl<'v> ComplexValue<'v> for RecordType<'v> {
    // So we can get the name set
    fn is_mutable(&self) -> bool {
        true
    }

    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        let mut fields = SmallMap::with_capacity(self.fields.len());
        for (k, t) in self.fields.into_iter_hashed() {
            fields.insert_hashed(k, t.freeze(freezer));
        }
        box FrozenRecordType {
            typ: self.typ,
            fields,
            constructor: self.constructor.freeze(freezer),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        self.fields.values_mut().for_each(|v| v.walk(walker));
        walker.walk(&mut self.constructor);
    }

    fn export_as(&mut self, _heap: &'v Heap, variable_name: &str) {
        if self.typ.is_none() {
            self.typ = Some(variable_name.to_owned())
        }
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for RecordTypeGen<V>
where
    Self: AnyLifetime<'v>,
    FieldGen<V>: AnyLifetime<'v>,
{
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collect_repr_record(self.fields.iter(), |x, s| x.collect_repr(s), collector);
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        for (name, typ) in &self.fields {
            name.hash(&mut s);
            s.write_u64(typ.get_hash()?);
        }
        Ok(s.finish())
    }

    fn new_invoker(
        &self,
        me: Value<'v>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<FunctionInvoker<'v>> {
        let mut f = self.constructor.new_invoker(eval)?;
        f.push_pos(me, eval);
        Ok(f)
    }

    fn dir_attr(&self) -> Vec<String> {
        vec!["type".to_owned()]
    }

    fn has_attr(&self, attribute: &str) -> bool {
        attribute == "type"
    }

    fn get_attr(&self, attribute: &str, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if attribute == "type" {
            Ok(heap.alloc(self.typ.as_deref().unwrap_or(Record::TYPE)))
        } else {
            Err(ValueError::OperationNotSupported {
                op: attribute.to_owned(),
                typ: self.to_repr(),
            }
            .into())
        }
    }
}

impl<'v> ComplexValue<'v> for Record<'v> {
    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        box FrozenRecord {
            typ: self.typ.freeze(freezer),
            values: self.values.map(|v| v.freeze(freezer)),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        walker.walk(&mut self.typ);
        self.values.iter_mut().for_each(|v| walker.walk(v));
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for RecordGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(Record::TYPE);

    fn matches_type(&self, ty: &str) -> bool {
        ty == Record::TYPE || Some(ty) == self.get_record_type().typ.as_deref()
    }

    fn to_json(&self) -> anyhow::Result<String> {
        let mut s = "{".to_owned();
        s += &self
            .get_record_type()
            .fields
            .keys()
            .zip(&self.values)
            .map(|(k, v)| Ok(format!("\"{}\":{}", k, v.to_json()?)))
            .collect::<anyhow::Result<Vec<String>>>()?
            .join(",");
        s += "}";
        Ok(s)
    }

    fn collect_repr(&self, collector: &mut String) {
        collect_repr_record(
            self.get_record_type().fields.keys().zip(&self.values),
            |x, s| x.collect_repr(s),
            collector,
        );
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        // The type uses reference equality, since we didn't define an equals() for RecordType.
        // That's very probably the right thing to do.
        match Record::from_value(other) {
            Some(other) if self.typ.equals(other.typ)? => {
                equals_slice(&self.values, &other.values, |x, y| x.equals(*y))
            }
            _ => Ok(false),
        }
    }

    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match self.get_record_type().fields.get_index_of(attribute) {
            Some(i) => Ok(self.values[i].to_value()),
            None => Err(ValueError::OperationNotSupported {
                op: attribute.to_owned(),
                typ: self.to_repr(),
            }
            .into()),
        }
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        s.write_u64(self.typ.get_hash()?);
        for v in &self.values {
            s.write_u64(v.get_hash()?);
        }
        Ok(s.finish())
    }

    fn has_attr(&self, attribute: &str) -> bool {
        self.get_record_type().fields.contains_key(attribute)
    }

    fn dir_attr(&self) -> Vec<String> {
        self.get_record_type().fields.keys().cloned().collect()
    }
}
