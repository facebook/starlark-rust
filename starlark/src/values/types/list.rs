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

//! The list type, a mutable sequence of values.

use crate::{
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::{compare_slice, equals_slice},
        error::ValueError,
        index::{convert_index, convert_slice_indices},
        iter::StarlarkIterable,
        tuple, AllocFrozenValue, AllocValue, ComplexValue, Freezer, FrozenHeap, FrozenValue, Heap,
        SimpleValue, StarlarkValue, Tracer, UnpackValue, Value, ValueLike,
    },
};
use gazebo::{any::AnyLifetime, cell::ARef, prelude::*};
use std::{cmp::Ordering, marker::PhantomData, ops::Deref};

/// Define the list type. See [`List`] and [`FrozenList`] as the two aliases.
#[derive(Clone, Default_, Debug)]
pub struct ListGen<V> {
    /// The data stored by the list.
    pub content: Vec<V>,
}

impl<V> ListGen<V> {
    /// The result of calling `type()` on lists.
    pub const TYPE: &'static str = "list";
}

starlark_complex_value!(pub List);

impl<'v, V: AllocValue<'v>> AllocValue<'v> for Vec<V> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_complex(List {
            content: self.into_map(|x| x.alloc_value(heap)),
        })
    }
}

impl<'v, V: AllocFrozenValue> AllocFrozenValue for Vec<V> {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(FrozenList {
            content: self.into_map(|x| x.alloc_frozen_value(heap)),
        })
    }
}

impl FrozenList {
    /// Obtain the [`FrozenList`] pointed at by a [`FrozenValue`].
    #[allow(clippy::trivially_copy_pass_by_ref)]
    // We need a lifetime because FrozenValue doesn't contain the right lifetime
    pub fn from_frozen_value(x: &FrozenValue) -> Option<ARef<FrozenList>> {
        x.downcast_ref::<FrozenList>()
    }
}

impl<'v> ComplexValue<'v> for List<'v> {
    fn is_mutable(&self) -> bool {
        true
    }

    fn freeze(self: Box<Self>, freezer: &Freezer) -> anyhow::Result<Box<dyn SimpleValue>> {
        let mut content = Vec::with_capacity(self.content.len());
        for v in self.content {
            content.push(v.freeze(freezer)?)
        }
        Ok(box FrozenList { content })
    }

    unsafe fn walk(&mut self, walker: &Tracer<'v>) {
        self.content.iter_mut().for_each(|x| walker.walk(x))
    }

    fn set_at(
        &mut self,
        me: Value<'v>,
        index: Value<'v>,
        alloc_value: Value<'v>,
    ) -> anyhow::Result<()> {
        if me.ptr_eq(index) {
            // since me is a list, index must be a list, which isn't right
            return Err(ValueError::IncorrectParameterTypeNamed("index".to_owned()).into());
        }
        let i = convert_index(index, self.len() as i32)? as usize;
        self.content[i] = alloc_value;
        Ok(())
    }
}

impl<'v, V: ValueLike<'v>> ListGen<V> {
    /// Create a new list.
    pub fn new(content: Vec<V>) -> Self {
        Self { content }
    }

    /// Obtain the length of the list.
    pub fn len(&self) -> usize {
        self.content.len()
    }

    /// Iterate over the elements in the list.
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = Value<'v>> + 'a
    where
        'v: 'a,
    {
        self.content.iter().map(|e| e.to_value())
    }
}

impl<'v> List<'v> {
    /// Append a single element to the end of the list.
    pub fn push(&mut self, value: Value<'v>) {
        self.content.push(value);
    }

    /// Append a series of elements to the end of the list.
    pub fn extend(&mut self, other: Vec<Value<'v>>) {
        self.content.extend(other);
    }

    /// Clear all elements in the list.
    pub fn clear(&mut self) {
        self.content.clear();
    }

    /// Find the position of a given element in the list.
    pub fn position(&self, needle: Value<'v>) -> Option<usize> {
        self.content.iter().position(|v| v == &needle)
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for ListGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(List::TYPE);

    fn get_methods(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.methods(crate::stdlib::list::list_methods)
    }

    fn collect_repr(&self, s: &mut String) {
        s.push('[');
        let mut first = true;
        for v in &self.content {
            if first {
                first = false;
            } else {
                s.push_str(", ");
            }
            v.collect_repr(s);
        }
        s.push(']');
    }

    fn to_json(&self) -> anyhow::Result<String> {
        let mut res = String::new();
        res.push('[');
        for (i, e) in self.content.iter().enumerate() {
            if i != 0 {
                res.push_str(", ");
            }
            res.push_str(&e.to_json()?);
        }
        res.push(']');
        Ok(res)
    }

    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match List::from_value(other) {
            None => Ok(false),
            Some(other) => equals_slice(&self.content, &other.content, |x, y| x.equals(*y)),
        }
    }

    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        match List::from_value(other) {
            None => ValueError::unsupported_with(self, "cmp()", other),
            Some(other) => compare_slice(&self.content, &other.content, |x, y| x.compare(*y)),
        }
    }

    fn at(&self, index: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let i = convert_index(index, self.len() as i32)? as usize;
        Ok(self.content[i].to_value())
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(self.content.len() as i32)
    }

    fn is_in(&self, other: Value<'v>) -> anyhow::Result<bool> {
        for x in self.content.iter() {
            if x.equals(other)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        let (start, stop, stride) = convert_slice_indices(self.len() as i32, start, stop, stride)?;
        let vec = tuple::slice_vector(start, stop, stride, self.content.iter());

        Ok(heap.alloc(List { content: vec }))
    }

    fn iterate(&self) -> anyhow::Result<&(dyn StarlarkIterable<'v> + 'v)> {
        Ok(self)
    }

    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = List::from_value(other) {
            let mut result = List {
                content: Vec::with_capacity(self.len() + other.len()),
            };
            for x in &self.content {
                result.content.push(x.to_value());
            }
            for x in other.iter() {
                result.content.push(x);
            }
            Ok(heap.alloc(result))
        } else {
            ValueError::unsupported_with(self, "+", other)
        }
    }

    fn mul(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_int() {
            Some(l) => {
                let mut result = List {
                    content: Vec::new(),
                };
                for _i in 0..l {
                    result
                        .content
                        .extend(self.content.iter().map(|x| ValueLike::to_value(*x)));
                }
                Ok(heap.alloc(result))
            }
            None => Err(ValueError::IncorrectParameterType.into()),
        }
    }
}

impl<'v, V: ValueLike<'v>> StarlarkIterable<'v> for ListGen<V> {
    fn to_iter<'a>(&'a self, _heap: &'v Heap) -> Box<dyn Iterator<Item = Value<'v>> + 'a>
    where
        'v: 'a,
    {
        box self.iter()
    }
}

/// Like `ValueOf`, but only validates item types; does not construct or store a
/// vec. Use `to_vec` to get a Vec.
pub struct ListOf<'v, V: UnpackValue<'v>> {
    value: Value<'v>,
    phantom: PhantomData<V>,
}

impl<'v, V: UnpackValue<'v>> ListOf<'v, V> {
    pub fn to_vec(&self) -> Vec<V> {
        List::from_value(self.value)
            .expect("already validated as a list")
            .iter()
            .map(|v| V::unpack_value(v).expect("already validated value"))
            .collect()
    }
}

impl<'v, V: UnpackValue<'v>> UnpackValue<'v> for ListOf<'v, V> {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        let list = List::from_value(value)?;
        if list.iter().all(|v| V::unpack_value(v).is_some()) {
            Some(ListOf {
                value,
                phantom: PhantomData,
            })
        } else {
            None
        }
    }
}

impl<'v, V: UnpackValue<'v>> Deref for ListOf<'v, V> {
    type Target = Value<'v>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

#[cfg(test)]
mod tests {
    use crate::assert::{self, Assert};

    #[test]
    fn test_to_str() {
        assert::all_true(
            r#"
str([1, 2, 3]) == "[1, 2, 3]"
str([1, [2, 3]]) == "[1, [2, 3]]"
str([]) == "[]"
"#,
        );
    }

    #[test]
    fn test_mutate_list() {
        assert::is_true(
            r#"
v = [1, 2, 3]
v[1] = 1
v[2] = [2, 3]
v == [1, 1, [2, 3]]
"#,
        );
    }

    #[test]
    fn test_arithmetic_on_list() {
        assert::all_true(
            r#"
[1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
[1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
"#,
        );
    }

    #[test]
    fn test_value_alias() {
        assert::is_true(
            r#"
v1 = [1, 2, 3]
v2 = v1
v2[2] = 4
v1 == [1, 2, 4] and v2 == [1, 2, 4]
"#,
        );
    }

    #[test]
    fn test_mutating_imports() {
        let mut a = Assert::new();
        a.module(
            "x",
            r#"
frozen_list = [1, 2]
frozen_list += [4]
def frozen_list_result():
    return frozen_list
def list_result():
    return [1, 2, 4]
"#,
        );
        a.fail("load('x','frozen_list')\nfrozen_list += [1]", "Immutable");
        a.fail(
            "load('x','frozen_list_result')\nx = frozen_list_result()\nx += [1]",
            "Immutable",
        );
        a.is_true("load('x','list_result')\nx = list_result()\nx += [8]\nx == [1, 2, 4, 8]");
    }
}
