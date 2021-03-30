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

//! Module define the Starlark type Dict
use crate::{
    collections::{Hashed, SmallMap},
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::equals_small_map, error::ValueError, iter::StarlarkIterable,
        string::hash_string_value, ComplexValue, Freezer, FrozenValue, Heap, SimpleValue,
        StarlarkValue, Value, ValueLike, Walker,
    },
};
use gazebo::{any::AnyLifetime, cell::ARef, prelude::*};
use indexmap::Equivalent;
use std::hash::{Hash, Hasher};

/// Define the Dict type
#[derive(Clone, Default_, Debug)]
pub struct DictGen<T> {
    pub content: SmallMap<T, T>,
}

impl<T> DictGen<T> {
    pub const TYPE: &'static str = "dict";
}

starlark_value!(pub Dict);

impl FrozenDict {
    // We need a lifetime because FrozenValue doesn't contain the right lifetime
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn from_value(x: &FrozenValue) -> Option<ARef<FrozenDict>> {
        x.downcast_ref::<FrozenDict>()
    }
}

/// The Dict type
impl<V> DictGen<V> {
    pub fn new(content: SmallMap<V, V>) -> Self {
        Self { content }
    }

    pub fn get_content(&self) -> &SmallMap<V, V> {
        &self.content
    }
}

#[derive(Eq, PartialEq)]
pub struct ValueStr<'a>(&'a str);

impl<'a> Hash for ValueStr<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_string_value(self.0, state)
    }
}

impl<'v> Equivalent<Value<'v>> for ValueStr<'_> {
    fn equivalent(&self, key: &Value<'v>) -> bool {
        key.unpack_str() == Some(self.0)
    }
}

impl Equivalent<FrozenValue> for ValueStr<'_> {
    fn equivalent(&self, key: &FrozenValue) -> bool {
        key.unpack_str() == Some(self.0)
    }
}

impl<'v, T: ValueLike<'v>> DictGen<T>
where
    Value<'v>: Equivalent<T>,
    for<'a> ValueStr<'a>: Equivalent<T>,
{
    pub fn len(&self) -> usize {
        self.content.len()
    }

    pub fn items(&self) -> Vec<(Value<'v>, Value<'v>)> {
        self.content
            .iter()
            .map(|(k, v)| (k.to_value(), v.to_value()))
            .collect()
    }

    pub fn values(&self) -> Vec<Value<'v>> {
        self.content.values().map(|e| e.to_value()).collect()
    }

    pub fn keys(&self) -> Vec<Value<'v>> {
        self.content.keys().map(|e| e.to_value()).collect()
    }

    pub fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = (Value<'v>, Value<'v>)> + 'a> {
        box self
            .content
            .iter()
            .map(|(l, r)| (l.to_value(), r.to_value()))
    }

    pub fn iter_hashed<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (Hashed<Value<'v>>, Value<'v>)> + 'a> {
        box self
            .content
            .iter_hashed()
            .map(|(l, r)| (l.unborrow_copy().to_hashed_value(), r.to_value()))
    }

    pub fn get(&self, key: Value<'v>) -> anyhow::Result<Option<Value<'v>>> {
        Ok(self
            .content
            .get_hashed(key.get_hashed()?.borrow())
            .copied()
            .map(ValueLike::to_value))
    }

    pub fn get_str(&self, key: &str) -> Option<Value<'v>> {
        self.content
            .get(&ValueStr(key))
            .copied()
            .map(ValueLike::to_value)
    }
}

impl<'v> ComplexValue<'v> for Dict<'v> {
    fn is_mutable(&self) -> bool {
        true
    }

    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        let mut content: SmallMap<FrozenValue, FrozenValue> =
            SmallMap::with_capacity(self.content.len());
        for (k, v) in self.content.into_iter_hashed() {
            content.insert_hashed(k.freeze(freezer), v.freeze(freezer));
        }
        box FrozenDict { content }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        self.content.iter_mut().for_each(|(k, v)| {
            walker.walk_dictionary_key(k);
            walker.walk(v);
        })
    }

    fn set_at(&mut self, index: Value<'v>, alloc_value: Value<'v>) -> anyhow::Result<()> {
        let index = index.get_hashed()?;
        if let Some(x) = self.content.get_mut_hashed(index.borrow()) {
            *x = alloc_value;
            return Ok(());
        }
        self.content.insert_hashed(index, alloc_value);
        Ok(())
    }
}

impl FrozenDict {
    pub(crate) fn thaw<'v>(&self) -> Box<dyn ComplexValue<'v> + 'v> {
        let mut items = SmallMap::with_capacity(self.content.len());
        // We know all the contents of the dictionary will themselves be immutable
        for (k, v) in self.content.iter_hashed() {
            items.insert_hashed(k.unborrow_copy().to_hashed_value(), v.to_value());
        }
        box Dict { content: items }
    }
}

impl SimpleValue for FrozenDict {}

impl<'v, T: ValueLike<'v>> StarlarkValue<'v> for DictGen<T>
where
    Value<'v>: Equivalent<T>,
    T: Equivalent<Value<'v>>,
    Self: AnyLifetime<'v>,
{
    starlark_type!(Dict::TYPE);

    fn get_members(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.members(crate::stdlib::dict::dict_members)
    }

    fn collect_repr(&self, r: &mut String) {
        r.push('{');
        for (i, (name, value)) in self.content.iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            name.collect_repr(r);
            r.push_str(": ");
            value.collect_repr(r);
        }
        r.push('}');
    }

    fn to_json(&self) -> String {
        format!(
            "{{{}}}",
            self.content
                .iter()
                .map(|(k, v)| format!("{}: {}", k.to_json(), v.to_json()))
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                })
        )
    }

    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match Dict::from_value(other) {
            None => Ok(false),
            Some(other) => equals_small_map(&self.content, &other.content, |x, y| x.equals(*y)),
        }
    }

    fn at(&self, index: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match self.content.get_hashed(index.get_hashed()?.borrow()) {
            Some(v) => Ok(v.to_value()),
            None => Err(ValueError::KeyNotFound(index.to_repr()).into()),
        }
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(self.content.len() as i32)
    }

    fn is_in(&self, other: Value<'v>) -> anyhow::Result<bool> {
        Ok(self
            .content
            .contains_key_hashed(other.get_hashed()?.borrow()))
    }

    fn iterate(&self) -> anyhow::Result<&(dyn StarlarkIterable<'v> + 'v)> {
        Ok(self)
    }
}

impl<'v, T: ValueLike<'v>> StarlarkIterable<'v> for DictGen<T> {
    fn to_iter<'a>(&'a self, _heap: &'v Heap) -> Box<dyn Iterator<Item = Value<'v>> + 'a>
    where
        'v: 'a,
    {
        box self.content.iter().map(|x| x.0.to_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert, collections::SmallMap, values::Heap};

    #[test]
    fn test_mutate_dict() {
        assert::is_true(
            r#"
x = {1: 2, 2: 4}
b1 = str(x) == "{1: 2, 2: 4}"
x[2] = 3
b2 = str(x) == "{1: 2, 2: 3}"
x[(3,4)] = 5
b3 = str(x) == "{1: 2, 2: 3, (3, 4): 5}"
b1 and b2 and b3
"#,
        );
    }

    #[test]
    fn test_get_str() -> anyhow::Result<()> {
        let heap = Heap::new();
        let k1 = heap.alloc("hello");
        let k2 = heap.alloc("world");
        let mut sm = SmallMap::new();
        sm.insert_hashed(k1.get_hashed()?, Value::new_int(12));
        sm.insert_hashed(k2.get_hashed()?, Value::new_int(56));
        let d = Dict::new(sm);

        assert_eq!(d.get(heap.alloc("hello"))?.unwrap().unpack_int(), Some(12));
        assert_eq!(d.get(heap.alloc("foo"))?, None);
        assert_eq!(d.get_str("hello").unwrap().unpack_int(), Some(12));
        assert_eq!(d.get_str("foo"), None);
        Ok(())
    }
}
