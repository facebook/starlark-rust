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
    collections::SmallMap,
    values::{dict::Dict, list::List, Heap, UnpackValue, Value},
};
use std::{hash::Hash, marker::PhantomData, ops::Deref};

/// A wrapper that keeps the original value on the heap for use elsewhere in the
/// interpreter, and also, when unpacked, unpacks the value to validate it is of
/// the correct type.
///
/// Two container specializations of this are `ListOf` and `DictOf`, which
/// validate the types of their containers on unpack, but do not store the
/// resulting Vec/Map
#[derive(Debug)]
pub struct ValueOf<'v, T: UnpackValue<'v>> {
    pub value: Value<'v>,
    pub typed: T,
}

impl<'v, T: UnpackValue<'v>> Deref for ValueOf<'v, T> {
    type Target = Value<'v>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for ValueOf<'v, T> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let typed = T::unpack_value(value, heap)?;
        Some(Self { value, typed })
    }
}

/// Like `ValueOf`, but only validates key and value types; does not construct
/// or store a map. Use `to_dict` to get a map.
pub struct DictOf<'v, K: UnpackValue<'v> + Hash, V: UnpackValue<'v>> {
    value: Value<'v>,
    phantom: PhantomData<(K, V)>,
}

impl<'v, K: UnpackValue<'v> + Hash + Eq, V: UnpackValue<'v>> DictOf<'v, K, V> {
    pub fn to_dict(&self, heap: &'v Heap) -> SmallMap<K, V> {
        Dict::from_value(self.value)
            .expect("already validated as a dict")
            .iter()
            .map(|(k, v)| {
                (
                    K::unpack_value(k, heap).expect("already validated key"),
                    V::unpack_value(v, heap).expect("already validated value"),
                )
            })
            .collect()
    }
}

impl<'v, K: UnpackValue<'v> + Hash, V: UnpackValue<'v>> UnpackValue<'v> for DictOf<'v, K, V> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let dict = Dict::from_value(value)?;
        let all_valid = dict
            .iter()
            .all(|(k, v)| K::unpack_value(k, heap).is_some() && V::unpack_value(v, heap).is_some());
        if all_valid {
            Some(DictOf {
                value,
                phantom: PhantomData {},
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

/// Like `ValueOf`, but only validates item types; does not construct or store a
/// vec. Use `to_vec` to get a Vec.
pub struct ListOf<'v, T: UnpackValue<'v>> {
    value: Value<'v>,
    phantom: PhantomData<T>,
}

impl<'v, T: UnpackValue<'v>> ListOf<'v, T> {
    pub fn to_vec(&self, heap: &'v Heap) -> Vec<T> {
        List::from_value(self.value)
            .expect("already validated as a list")
            .iter()
            .map(|v| T::unpack_value(v, heap).expect("already validated value"))
            .collect()
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for ListOf<'v, T> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let list = List::from_value(value)?;
        if list.iter().all(|v| T::unpack_value(v, heap).is_some()) {
            Some(ListOf {
                value,
                phantom: PhantomData {},
            })
        } else {
            None
        }
    }
}

impl<'v, T: UnpackValue<'v>> Deref for ListOf<'v, T> {
    type Target = Value<'v>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate as starlark;
    use crate::{assert::Assert, environment::GlobalsBuilder};
    use itertools::Itertools;

    // TODO(pjameson): Figure out default values here. ValueOf<i32> = 5 should work.
    #[starlark_module]
    fn validate_module(builder: &mut GlobalsBuilder) {
        fn with_int(v: ValueOf<i32>) -> (Value<'v>, String) {
            Ok((*v, format!("{}", v.typed)))
        }
        fn with_int_list(v: ListOf<i32>) -> (Value<'v>, String) {
            let repr = v.to_vec(heap).iter().join(", ");
            Ok((*v, repr))
        }
        fn with_list_list(v: ListOf<ListOf<i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_vec(heap)
                .iter()
                .map(|l| l.to_vec(heap).iter().join(", "))
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_dict_list(v: ListOf<DictOf<i32, i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_vec(heap)
                .iter()
                .map(|l| {
                    l.to_dict(heap)
                        .iter()
                        .map(|(k, v)| format!("{}: {}", k, v))
                        .join(", ")
                })
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_int_dict(v: DictOf<i32, i32>) -> (Value<'v>, String) {
            let repr = v
                .to_dict(heap)
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v))
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_list_dict(v: DictOf<i32, ListOf<i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_dict(heap)
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v.to_vec(heap).iter().join(", ")))
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_dict_dict(v: DictOf<i32, DictOf<i32, i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_dict(heap)
                .iter()
                .map(|(k, v)| {
                    let inner_repr = v
                        .to_dict(heap)
                        .iter()
                        .map(|(k2, v2)| format!("{}:{}", k2, v2))
                        .join(", ");
                    format!("{}: {}", k, inner_repr)
                })
                .join(" + ");
            Ok((*v, repr))
        }
    }

    // The standard error these raise on incorrect types
    const BAD: &str = "Type of parameter";

    #[test]
    fn test_value_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("(1, '1')", "with_int(1)");
        a.fail("with_int(None)", BAD);
    }

    #[test]
    fn test_list_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("([1, 2, 3], '1, 2, 3')", "with_int_list([1, 2, 3])");
        a.fail("with_int_list(1)", BAD);
        a.fail("with_int_list([1, 'foo'])", BAD);
        a.fail("with_int_list([[]])", BAD);

        a.eq(
            "([[1, 2], [3]], '1, 2 + 3')",
            "with_list_list([[1, 2], [3]])",
        );

        let expected = r#"([{1: 2, 3: 4}, {5: 6}], "1: 2, 3: 4 + 5: 6")"#;
        let test = r#"with_dict_list([{1: 2, 3: 4}, {5: 6}])"#;
        a.eq(expected, test);
    }

    #[test]
    fn test_dict_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("({1: 2}, '1: 2')", "with_int_dict({1: 2})");
        a.fail(r#"with_int_dict(1)"#, BAD);
        a.fail(r#"with_int_dict({1: "str"})"#, BAD);
        a.fail(r#"with_int_dict({1: {}})"#, BAD);

        let expected = r#"({1: [2, 3], 4: [5]}, "1: 2, 3 + 4: 5")"#;
        let test = r#"with_list_dict({1: [2, 3], 4: [5]})"#;
        a.eq(expected, test);

        let expected = r#"({1: {2: 3, 4: 5}, 6: {7: 8}}, "1: 2:3, 4:5 + 6: 7:8")"#;
        let test = r#"with_dict_dict({1: {2: 3, 4: 5}, 6: {7: 8}})"#;
        a.eq(expected, test);
    }
}
