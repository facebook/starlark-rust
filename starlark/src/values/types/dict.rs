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

//! The dictionary type, a mutable associative-map, which iterates in insertion order.

use crate as starlark;
use crate::{
    collections::{Hashed, SmallMap},
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::equals_small_map, error::ValueError, iter::ARefIterator,
        string::hash_string_value, AllocFrozenValue, AllocValue, ComplexValue, Freezer, FromValue,
        FrozenHeap, FrozenStringValue, FrozenValue, Heap, SimpleValue, StarlarkValue, Trace,
        UnpackValue, Value, ValueLike,
    },
};
use gazebo::{
    any::AnyLifetime,
    cell::ARef,
    coerce::{coerce_ref, Coerce},
};
use indexmap::Equivalent;
use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::Debug,
    hash::{Hash, Hasher},
    intrinsics::unlikely,
    marker::PhantomData,
    ops::Deref,
};

#[derive(Clone, Default, Trace, Debug)]
struct DictGen<T>(T);

/// Define the list type. See [`Dict`] and [`FrozenDict`] as the two possible representations.
#[derive(Clone, Default, Trace, Debug)]
#[repr(transparent)]
pub struct Dict<'v> {
    /// The data stored by the dictionary. The keys must all be hashable values.
    pub content: SmallMap<Value<'v>, Value<'v>>,
}

/// Define the list type. See [`Dict`] and [`FrozenDict`] as the two possible representations.
#[derive(Clone, Default, Debug, AnyLifetime)]
#[repr(transparent)]
pub struct FrozenDict {
    /// The data stored by the dictionary. The keys must all be hashable values.
    pub content: SmallMap<FrozenValue, FrozenValue>,
}

unsafe impl<'v> AnyLifetime<'v> for DictGen<RefCell<Dict<'v>>> {
    any_lifetime_body!(DictGen<RefCell<Dict<'static>>>);
}
any_lifetime!(DictGen<FrozenDict>);

unsafe impl<'v> Coerce<Dict<'v>> for FrozenDict {}

impl<'v> AllocValue<'v> for Dict<'v> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_complex(DictGen(RefCell::new(self)))
    }
}

impl AllocFrozenValue for FrozenDict {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(DictGen(self))
    }
}

impl SimpleValue for DictGen<FrozenDict> {}

impl<'v> Dict<'v> {
    pub fn from_value(x: Value<'v>) -> Option<ARef<'v, Self>> {
        if x.unpack_frozen().is_some() {
            x.downcast_ref::<DictGen<FrozenDict>>()
                .map(|x| ARef::new_ptr(coerce_ref(&x.0)))
        } else {
            let ptr = x.downcast_ref::<DictGen<RefCell<Dict<'v>>>>()?;
            Some(ARef::new_ref(ptr.0.borrow()))
        }
    }

    pub fn from_value_mut(x: Value<'v>) -> anyhow::Result<Option<RefMut<'v, Self>>> {
        if unlikely(x.unpack_frozen().is_some()) {
            return Err(ValueError::CannotMutateImmutableValue.into());
        }
        let ptr = x.downcast_ref::<DictGen<RefCell<Dict<'v>>>>();
        match ptr {
            None => Ok(None),
            Some(ptr) => match ptr.0.try_borrow_mut() {
                Ok(x) => Ok(Some(x)),
                Err(_) => Err(ValueError::MutationDuringIteration.into()),
            },
        }
    }
}

impl<'v> FromValue<'v> for Dict<'v> {
    fn from_value(x: Value<'v>) -> Option<ARef<'v, Self>> {
        Dict::from_value(x)
    }
}

impl FrozenDict {
    /// Obtain the [`FrozenDict`] pointed at by a [`FrozenValue`].
    #[allow(clippy::trivially_copy_pass_by_ref)]
    // We need a lifetime because FrozenValue doesn't contain the right lifetime
    pub fn from_frozen_value(x: &FrozenValue) -> Option<&FrozenDict> {
        x.downcast_ref::<DictGen<FrozenDict>>().map(|x| &x.0)
    }
}

/// Helper type for lookups, not useful.
#[derive(Eq, PartialEq)]
pub struct ValueStr<'a>(pub(crate) &'a str);

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

impl<'v> Dict<'v> {
    /// The result of calling `type()` on dictionaries.
    pub const TYPE: &'static str = "dict";

    pub fn get_type_value_static() -> FrozenStringValue {
        DictGen::<FrozenDict>::get_type_value_static()
    }

    /// Create a new [`Dict`].
    pub fn new(content: SmallMap<Value<'v>, Value<'v>>) -> Self {
        Self { content }
    }

    /// Iterate through the key/value pairs in the dictionary.
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (Value<'v>, Value<'v>)> + 'a
    where
        'v: 'a,
    {
        self.content.iter().map(|(l, r)| (*l, *r))
    }

    /// Iterate through the key/value pairs in the dictionary, but retaining the hash of the keys.
    pub fn iter_hashed<'a>(&'a self) -> impl Iterator<Item = (Hashed<Value<'v>>, Value<'v>)> + 'a
    where
        'v: 'a,
    {
        self.content
            .iter_hashed()
            .map(|(l, r)| (l.unborrow_copy(), *r))
    }

    /// Get the value associated with a particular key. Will be [`Err`] if the key is not hashable,
    /// and otherwise [`Some`] if the key exists in the dictionary and [`None`] otherwise.
    pub fn get(&self, key: Value<'v>) -> anyhow::Result<Option<Value<'v>>> {
        Ok(self.content.get_hashed(key.get_hashed()?.borrow()).copied())
    }

    /// Get the value associated with a particular string. Equivalent to allocating the
    /// string on the heap, turning it into a value, and looking up using that.
    pub fn get_str(&self, key: &str) -> Option<Value<'v>> {
        self.content.get(&ValueStr(key)).copied()
    }
}

impl FrozenDict {
    /// Iterate through the key/value pairs in the dictionary.
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (FrozenValue, FrozenValue)> + 'a {
        self.content.iter().map(|(l, r)| (*l, *r))
    }

    /// Iterate through the key/value pairs in the dictionary, but retaining the hash of the keys.
    pub fn iter_hashed<'a>(
        &'a self,
    ) -> impl Iterator<Item = (Hashed<FrozenValue>, FrozenValue)> + 'a {
        self.content
            .iter_hashed()
            .map(|(l, r)| (l.unborrow_copy(), *r))
    }

    /// Get the value associated with a particular key. Will be [`Err`] if the key is not hashable,
    /// and otherwise [`Some`] if the key exists in the dictionary and [`None`] otherwise.
    pub fn get<'v>(&self, key: Value<'v>) -> anyhow::Result<Option<FrozenValue>> {
        Ok(self.content.get_hashed(key.get_hashed()?.borrow()).copied())
    }

    /// Get the value associated with a particular string. Equivalent to allocating the
    /// string on the heap, turning it into a value, and looking up using that.
    pub fn get_str(&self, key: &str) -> Option<FrozenValue> {
        self.content.get(&ValueStr(key)).copied()
    }
}

impl<'v> ComplexValue<'v> for DictGen<RefCell<Dict<'v>>> {
    type Frozen = DictGen<FrozenDict>;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        let old = self.0.into_inner().content;
        let mut content: SmallMap<FrozenValue, FrozenValue> = SmallMap::with_capacity(old.len());
        for (k, v) in old.into_iter_hashed() {
            content.insert_hashed(k.freeze(freezer)?, v.freeze(freezer)?);
        }
        Ok(DictGen(FrozenDict { content }))
    }
}

trait DictLike<'v>: Debug {
    fn content(&self) -> ARef<SmallMap<Value<'v>, Value<'v>>>;
    fn set_at(&self, index: Hashed<Value<'v>>, value: Value<'v>) -> anyhow::Result<()>;
}

impl<'v> DictLike<'v> for RefCell<Dict<'v>> {
    fn content(&self) -> ARef<SmallMap<Value<'v>, Value<'v>>> {
        ARef::new_ref(Ref::map(self.borrow(), |x| &x.content))
    }

    fn set_at(&self, index: Hashed<Value<'v>>, alloc_value: Value<'v>) -> anyhow::Result<()> {
        match self.try_borrow_mut() {
            Ok(mut xs) => {
                xs.content.insert_hashed(index, alloc_value);
                Ok(())
            }
            Err(_) => Err(ValueError::MutationDuringIteration.into()),
        }
    }
}

impl<'v> DictLike<'v> for FrozenDict {
    fn content(&self) -> ARef<SmallMap<Value<'v>, Value<'v>>> {
        ARef::new_ptr(coerce_ref(&self.content))
    }

    fn set_at(&self, _index: Hashed<Value<'v>>, _value: Value<'v>) -> anyhow::Result<()> {
        Err(ValueError::CannotMutateImmutableValue.into())
    }
}

impl<'v, T: DictLike<'v>> StarlarkValue<'v> for DictGen<T>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(Dict::TYPE);

    fn get_methods(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.methods(crate::stdlib::dict::dict_methods)
    }

    fn collect_repr(&self, r: &mut String) {
        r.push('{');
        for (i, (name, value)) in self.0.content().iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            name.collect_repr(r);
            r.push_str(": ");
            value.collect_repr(r);
        }
        r.push('}');
    }

    fn to_json(&self) -> anyhow::Result<String> {
        let mut res = String::new();
        res.push('{');
        for (i, (k, v)) in self.0.content().iter().enumerate() {
            if i != 0 {
                res.push_str(", ");
            }
            res.push_str(&k.to_json()?);
            res.push_str(": ");
            res.push_str(&v.to_json()?);
        }
        res.push('}');
        Ok(res)
    }

    fn to_bool(&self) -> bool {
        !self.0.content().is_empty()
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match Dict::from_value(other) {
            None => Ok(false),
            Some(other) => {
                equals_small_map(&*self.0.content(), &other.content, |x, y| x.equals(*y))
            }
        }
    }

    fn at(&self, index: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match self.0.content().get_hashed(index.get_hashed()?.borrow()) {
            Some(v) => Ok(v.to_value()),
            None => Err(ValueError::KeyNotFound(index.to_repr()).into()),
        }
    }

    fn extra_memory(&self) -> usize {
        self.0.content().extra_memory()
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(self.0.content().len() as i32)
    }

    fn is_in(&self, other: Value<'v>) -> anyhow::Result<bool> {
        Ok(self
            .0
            .content()
            .contains_key_hashed(other.get_hashed()?.borrow()))
    }

    fn iterate<'a>(
        &'a self,
        _heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'a>>
    where
        'v: 'a,
    {
        Ok(box ARefIterator::new(self.0.content(), |x| {
            x.keys().copied()
        }))
    }

    fn with_iterator(
        &self,
        _heap: &'v Heap,
        f: &mut dyn FnMut(&mut dyn Iterator<Item = Value<'v>>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        f(&mut self.0.content().keys().copied())
    }

    fn set_at(&self, index: Value<'v>, alloc_value: Value<'v>) -> anyhow::Result<()> {
        let index = index.get_hashed()?;
        self.0.set_at(index, alloc_value)
    }
}

impl<'v, K: UnpackValue<'v> + Hash + Eq, V: UnpackValue<'v>> UnpackValue<'v> for SmallMap<K, V> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        let dict = Dict::from_value(value)?;
        let mut r = SmallMap::new();
        for (k, v) in dict.content.iter() {
            r.insert(K::unpack_value(*k)?, V::unpack_value(*v)?);
        }
        Some(r)
    }
}

/// Like [`ValueOf`](crate::values::ValueOf), but only validates key and value types; does not construct
/// or store a map. Use `to_dict` to get at the map.
pub struct DictOf<'v, K: UnpackValue<'v> + Hash, V: UnpackValue<'v>> {
    value: Value<'v>,
    phantom: PhantomData<(K, V)>,
}

impl<'v, K: UnpackValue<'v> + Hash + Eq, V: UnpackValue<'v>> DictOf<'v, K, V> {
    pub fn to_dict(&self) -> SmallMap<K, V> {
        Dict::from_value(self.value)
            .expect("already validated as a dict")
            .iter()
            .map(|(k, v)| {
                (
                    K::unpack_value(k).expect("already validated key"),
                    V::unpack_value(v).expect("already validated value"),
                )
            })
            .collect()
    }
}

impl<'v, K: UnpackValue<'v> + Hash, V: UnpackValue<'v>> UnpackValue<'v> for DictOf<'v, K, V> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        let dict = Dict::from_value(value)?;
        let all_valid = dict
            .iter()
            .all(|(k, v)| K::unpack_value(k).is_some() && V::unpack_value(v).is_some());
        if all_valid {
            Some(DictOf {
                value,
                phantom: PhantomData,
            })
        } else {
            None
        }
    }
}

impl<'v, K: UnpackValue<'v> + Hash, V: UnpackValue<'v>> Deref for DictOf<'v, K, V> {
    type Target = Value<'v>;

    fn deref(&self) -> &Self::Target {
        &self.value
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
        let k1 = heap.alloc_str_hashed("hello");
        let k2 = heap.alloc_str_hashed("world");
        let mut sm = SmallMap::new();
        sm.insert_hashed(k1, Value::new_int(12));
        sm.insert_hashed(k2, Value::new_int(56));
        let d = Dict::new(sm);

        assert_eq!(d.get(heap.alloc("hello"))?.unwrap().unpack_int(), Some(12));
        assert_eq!(d.get(heap.alloc("foo"))?, None);
        assert_eq!(d.get_str("hello").unwrap().unpack_int(), Some(12));
        assert_eq!(d.get_str("foo"), None);
        Ok(())
    }
}
