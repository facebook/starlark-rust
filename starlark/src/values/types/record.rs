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

use crate as starlark;
use crate::{
    codemap::Span,
    collections::SmallMap,
    eval::{Arguments, Evaluator, ParametersParser, ParametersSpec},
    values::{
        comparison::equals_slice,
        function::{NativeFunction, FUNCTION_TYPE},
        typing::TypeCompiled,
        ComplexValue, Freezer, FrozenValue, Heap, StarlarkValue, Trace, Value, ValueLike,
    },
};
use either::Either;
use gazebo::{
    any::AnyLifetime,
    cell::AsARef,
    coerce::{coerce_ref, Coerce},
    prelude::*,
};
use std::{
    cell::RefCell,
    collections::hash_map::DefaultHasher,
    fmt::Debug,
    hash::{Hash, Hasher},
};

/// The result of `field()`.
#[derive(Clone, Debug, Dupe, Trace)]
pub struct FieldGen<V> {
    pub(crate) typ: V,
    default: Option<V>,
}

// Manual because no instance for Option<V>
unsafe impl<From: Coerce<To>, To> Coerce<FieldGen<To>> for FieldGen<From> {}

/// The result of `record()`, being the type of records.
#[derive(Debug, Trace)]
pub struct RecordTypeGen<V, Typ> {
    /// The name of this type, e.g. MyRecord
    /// Either `Option<String>` or a `RefCell` thereof.
    typ: Typ,
    /// The V is the type the field must satisfy (e.g. `"string"`)
    fields: SmallMap<String, (FieldGen<V>, TypeCompiled)>,
    /// The construction function, which takes a hidden parameter (this type)
    /// followed by the arguments of the field.
    /// Creating these on every invoke is pretty expensive (profiling shows)
    /// so compute them in advance and cache.
    constructor: V,
}

pub type RecordType<'v> = RecordTypeGen<Value<'v>, RefCell<Option<String>>>;
pub type FrozenRecordType = RecordTypeGen<FrozenValue, Option<String>>;

/// An actual record.
#[derive(Clone, Debug, Trace, Coerce)]
#[repr(C)]
pub struct RecordGen<V> {
    typ: V, // Must be RecordType
    values: Vec<V>,
}

starlark_complex_value!(pub(crate) Field);
starlark_complex_values!(RecordType);
starlark_complex_value!(pub Record);

impl<V> FieldGen<V> {
    pub(crate) fn new(typ: V, default: Option<V>) -> Self {
        Self { typ, default }
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

fn record_fields<'v>(
    x: Either<&'v RecordType<'v>, &'v FrozenRecordType>,
) -> &'v SmallMap<String, (FieldGen<Value<'v>>, TypeCompiled)> {
    x.either(|x| &x.fields, |x| coerce_ref(&x.fields))
}

impl<'v> RecordType<'v> {
    pub(crate) fn new(
        fields: SmallMap<String, (FieldGen<Value<'v>>, TypeCompiled)>,
        heap: &'v Heap,
    ) -> Self {
        let constructor = heap.alloc(Self::make_constructor(&fields));
        Self {
            typ: RefCell::new(None),
            fields,
            constructor,
        }
    }

    fn make_constructor(
        fields: &SmallMap<String, (FieldGen<Value<'v>>, TypeCompiled)>,
    ) -> NativeFunction {
        let mut parameters = ParametersSpec::with_capacity("record".to_owned(), fields.len());
        parameters.no_args();
        for (name, field) in fields {
            if field.0.default.is_some() {
                parameters.optional(name);
            } else {
                parameters.required(name);
            }
        }

        // We want to get the value of `me` into the function, but that doesn't work since it
        // might move between threads - so we create the NativeFunction and apply it later.
        NativeFunction::new(
            move |eval, this, mut param_parser: ParametersParser| {
                let this = this.unwrap();
                let fields = record_fields(RecordType::from_value(this).unwrap());
                let mut values = Vec::with_capacity(fields.len());
                for (name, field) in fields.iter() {
                    match field.0.default {
                        None => {
                            let v: Value = param_parser.next(name)?;
                            v.check_type_compiled(field.0.typ, &field.1, Some(name))?;
                            values.push(v);
                        }
                        Some(default) => {
                            let v: Option<Value> = param_parser.next_opt(name)?;
                            match v {
                                None => values.push(default),
                                Some(v) => {
                                    v.check_type_compiled(field.0.typ, &field.1, Some(name))?;
                                    values.push(v);
                                }
                            }
                        }
                    }
                }
                Ok(eval.heap().alloc_complex(Record { typ: this, values }))
            },
            parameters.signature(),
            parameters,
        )
    }
}

impl<'v, V: ValueLike<'v>> RecordGen<V> {
    pub const TYPE: &'static str = "record";

    fn get_record_type(&self) -> Either<&'v RecordType<'v>, &'v FrozenRecordType> {
        // Safe to unwrap because we always ensure typ is RecordType
        RecordType::from_value(self.typ.to_value()).unwrap()
    }

    fn get_record_fields(&self) -> &'v SmallMap<String, (FieldGen<Value<'v>>, TypeCompiled)> {
        record_fields(self.get_record_type())
    }
}

impl<'v> ComplexValue<'v> for Field<'v> {
    type Frozen = FrozenField;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        Ok(FrozenField {
            typ: self.typ.freeze(freezer)?,
            default: self.default.into_try_map(|x| x.freeze(freezer))?,
        })
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
    type Frozen = FrozenRecordType;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        let mut fields = SmallMap::with_capacity(self.fields.len());
        for (k, t) in self.fields.into_iter_hashed() {
            fields.insert_hashed(k, (t.0.freeze(freezer)?, t.1));
        }
        Ok(FrozenRecordType {
            typ: self.typ.into_inner(),
            fields,
            constructor: self.constructor.freeze(freezer)?,
        })
    }
}

impl<'v, Typ, V: ValueLike<'v>> StarlarkValue<'v> for RecordTypeGen<V, Typ>
where
    Self: AnyLifetime<'v>,
    FieldGen<V>: AnyLifetime<'v>,
    Typ: AsARef<Option<String>> + Debug,
{
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collect_repr_record(self.fields.iter(), |x, s| x.0.collect_repr(s), collector);
    }

    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        for (name, typ) in &self.fields {
            name.hash(&mut s);
            // No need to hash typ.1, since it was computed from typ.0
            s.write_u64(typ.0.get_hash()?);
        }
        Ok(s.finish())
    }

    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        mut args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        args.this = Some(me);
        self.constructor.invoke(location, args, eval)
    }

    fn extra_memory(&self) -> usize {
        // We don't capture the memory beneath the TypeCompiled, since we don't know how big
        // those closures are.
        let typ = self.typ.as_aref();
        typ.as_ref().map_or(0, |s| s.capacity()) + self.fields.extra_memory()
    }

    fn dir_attr(&self) -> Vec<String> {
        vec!["type".to_owned()]
    }

    fn has_attr(&self, attribute: &str) -> bool {
        attribute == "type"
    }

    fn get_attr(&self, attribute: &str, heap: &'v Heap) -> Option<Value<'v>> {
        if attribute == "type" {
            Some(heap.alloc(self.typ.as_aref().as_deref().unwrap_or(Record::TYPE)))
        } else {
            None
        }
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        fn eq<'v>(
            a: &RecordTypeGen<impl ValueLike<'v>, impl AsARef<Option<String>>>,
            b: &RecordTypeGen<impl ValueLike<'v>, impl AsARef<Option<String>>>,
        ) -> anyhow::Result<bool> {
            if a.typ.as_aref() != b.typ.as_aref() {
                return Ok(false);
            };
            if a.fields.len() != b.fields.len() {
                return Ok(false);
            };
            for ((k1, t1), (k2, t2)) in a.fields.iter().zip(b.fields.iter()) {
                // We require that the types and defaults are both equal.
                if k1 != k2
                    || !t1.0.typ.equals(t2.0.typ.to_value())?
                    || t1.0.default.map(ValueLike::to_value)
                        != t2.0.default.map(ValueLike::to_value)
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }

        match RecordType::from_value(other) {
            Some(Either::Left(other)) => eq(self, &*other),
            Some(Either::Right(other)) => eq(self, &*other),
            _ => Ok(false),
        }
    }

    fn export_as(&self, variable_name: &str, _eval: &mut Evaluator<'v, '_>) {
        if let Some(typ) = self.typ.as_ref_cell() {
            let mut typ = typ.borrow_mut();
            if typ.is_none() {
                *typ = Some(variable_name.to_owned())
            }
        }
    }
}

impl<'v> ComplexValue<'v> for Record<'v> {
    type Frozen = FrozenRecord;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        Ok(FrozenRecord {
            typ: self.typ.freeze(freezer)?,
            values: self.values.try_map(|v| v.freeze(freezer))?,
        })
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for RecordGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(Record::TYPE);

    fn matches_type(&self, ty: &str) -> bool {
        if ty == Record::TYPE {
            return true;
        }
        match self.get_record_type() {
            Either::Left(x) => Some(ty) == x.typ.borrow().as_deref(),
            Either::Right(x) => Some(ty) == x.typ.as_deref(),
        }
    }

    fn to_json(&self) -> anyhow::Result<String> {
        let mut s = "{".to_owned();
        s += &self
            .get_record_fields()
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
            self.get_record_fields().keys().zip(&self.values),
            |x, s| x.collect_repr(s),
            collector,
        );
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match Record::from_value(other) {
            Some(other) if self.typ.equals(other.typ)? => {
                equals_slice(&self.values, &other.values, |x, y| x.equals(*y))
            }
            _ => Ok(false),
        }
    }

    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> Option<Value<'v>> {
        let i = self.get_record_fields().get_index_of(attribute)?;
        Some(self.values[i].to_value())
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
        self.get_record_fields().contains_key(attribute)
    }

    fn dir_attr(&self) -> Vec<String> {
        self.get_record_fields().keys().cloned().collect()
    }
}
