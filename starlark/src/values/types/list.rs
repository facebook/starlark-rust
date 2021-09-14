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

use crate as starlark;
use crate::{
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::{compare_slice, equals_slice},
        error::ValueError,
        index::{apply_slice, convert_index},
        iter::ARefIterator,
        AllocFrozenValue, AllocValue, ComplexValue, Freezer, FromValue, FrozenHeap,
        FrozenStringValue, FrozenValue, Heap, SimpleValue, StarlarkValue, UnpackValue, Value,
        ValueLike,
    },
};
use gazebo::{
    any::AnyLifetime,
    cell::ARef,
    coerce::{coerce_ref, Coerce},
    prelude::*,
};
use std::{
    any::TypeId,
    cell::{Ref, RefCell},
    cmp,
    cmp::Ordering,
    fmt::Debug,
    intrinsics::unlikely,
    marker::PhantomData,
    mem,
    ops::Deref,
};

#[derive(Clone, Default, Trace, Debug)]
struct ListGen<T>(T);

/// Define the list type. See [`List`] and [`FrozenList`] as the two possible representations.
#[derive(Clone, Default, Trace, Debug, AnyLifetime)]
#[repr(transparent)]
pub struct List<'v> {
    /// The data stored by the list.
    pub content: Vec<Value<'v>>,
}

/// Define the list type. See [`List`] and [`FrozenList`] as the two possible representations.
#[derive(Clone, Default, Debug, AnyLifetime)]
#[repr(transparent)]
pub struct FrozenList {
    /// The data stored by the list.
    pub content: Vec<FrozenValue>,
}

unsafe impl<'v> AnyLifetime<'v> for ListGen<RefCell<List<'v>>> {
    any_lifetime_body!(ListGen<RefCell<List<'static>>>);
}
any_lifetime!(ListGen<FrozenList>);

unsafe impl<'v> Coerce<List<'v>> for FrozenList {}

impl<'v> AllocValue<'v> for List<'v> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_complex(ListGen(RefCell::new(self)))
    }
}

impl AllocFrozenValue for FrozenList {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(ListGen(self))
    }
}

impl SimpleValue for ListGen<FrozenList> {}

impl<'v> List<'v> {
    pub fn from_value(x: Value<'v>) -> Option<ARef<'v, Self>> {
        if x.unpack_frozen().is_some() {
            x.downcast_ref::<ListGen<FrozenList>>()
                .map(|x| ARef::new_ptr(coerce_ref(&x.0)))
        } else {
            let ptr = x.downcast_ref::<ListGen<RefCell<List>>>()?;
            Some(ARef::new_ref(ptr.0.borrow()))
        }
    }

    pub fn from_value_mut(x: Value<'v>) -> anyhow::Result<Option<std::cell::RefMut<'v, Self>>> {
        if unlikely(x.unpack_frozen().is_some()) {
            return Err(ValueError::CannotMutateImmutableValue.into());
        }
        let ptr = x.downcast_ref::<ListGen<RefCell<List<'v>>>>();
        match ptr {
            None => Ok(None),
            Some(ptr) => match ptr.0.try_borrow_mut() {
                Ok(x) => Ok(Some(x)),
                Err(_) => Err(ValueError::MutationDuringIteration.into()),
            },
        }
    }

    pub(crate) fn is_list_type(x: TypeId) -> bool {
        x == TypeId::of::<ListGen<RefCell<List>>>() || x == TypeId::of::<ListGen<FrozenList>>()
    }
}

impl<'v> FromValue<'v> for List<'v> {
    fn from_value(x: Value<'v>) -> Option<ARef<'v, Self>> {
        List::from_value(x)
    }
}

impl<'v, V: AllocValue<'v>> AllocValue<'v> for Vec<V> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc(List::new(self.into_map(|x| x.alloc_value(heap))))
    }
}

impl<'v, V: AllocFrozenValue> AllocFrozenValue for Vec<V> {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc(FrozenList {
            content: self.into_map(|x| x.alloc_frozen_value(heap)),
        })
    }
}

impl<'a, 'v, V: 'a> AllocValue<'v> for &'a [V]
where
    &'a V: AllocValue<'v>,
{
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc(List::new(self.map(|x| x.alloc_value(heap))))
    }
}

impl<'a, 'v, V: 'a> AllocFrozenValue for &'a [V]
where
    &'a V: AllocFrozenValue,
{
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc(FrozenList {
            content: self.map(|x| x.alloc_frozen_value(heap)),
        })
    }
}

impl FrozenList {
    /// Obtain the [`FrozenList`] pointed at by a [`FrozenValue`].
    #[allow(clippy::trivially_copy_pass_by_ref)]
    // We need a lifetime because FrozenValue doesn't contain the right lifetime
    pub fn from_frozen_value(x: &FrozenValue) -> Option<&FrozenList> {
        x.downcast_ref::<ListGen<FrozenList>>().map(|x| &x.0)
    }
}

impl<'v> ComplexValue<'v> for ListGen<RefCell<List<'v>>> {
    type Frozen = ListGen<FrozenList>;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        Ok(ListGen(FrozenList {
            content: self
                .0
                .into_inner()
                .content
                .into_try_map(|v| v.freeze(freezer))?,
        }))
    }
}

impl<'v> List<'v> {
    /// The result of calling `type()` on lists.
    pub const TYPE: &'static str = "list";

    pub fn get_type_value_static() -> FrozenStringValue {
        ListGen::<FrozenList>::get_type_value_static()
    }

    pub fn new(content: Vec<Value<'v>>) -> Self {
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
        self.content.iter().copied()
    }

    pub fn to_repr(&self) -> String {
        let mut s = String::new();
        collect_repr(&self.content, &mut s);
        s
    }
}

impl FrozenList {
    /// Iterate over the elements in the list.
    pub fn iter<'a, 'v>(&'a self) -> impl Iterator<Item = Value<'v>> + 'a
    where
        'v: 'a,
    {
        self.content.iter().map(|e| e.to_value())
    }
}

trait ListLike<'v>: Debug {
    fn content(&self) -> ARef<Vec<Value<'v>>>;
    fn set_at(&self, i: usize, v: Value<'v>) -> anyhow::Result<()>;
}

impl<'v> ListLike<'v> for RefCell<List<'v>> {
    fn content(&self) -> ARef<Vec<Value<'v>>> {
        ARef::new_ref(Ref::map(self.borrow(), |x| &x.content))
    }

    fn set_at(&self, i: usize, v: Value<'v>) -> anyhow::Result<()> {
        match self.try_borrow_mut() {
            Ok(mut xs) => {
                xs.content[i] = v;
                Ok(())
            }
            Err(_) => Err(ValueError::MutationDuringIteration.into()),
        }
    }
}

impl<'v> ListLike<'v> for FrozenList {
    fn content(&self) -> ARef<Vec<Value<'v>>> {
        ARef::new_ptr(coerce_ref(&self.content))
    }

    fn set_at(&self, _i: usize, _v: Value<'v>) -> anyhow::Result<()> {
        Err(ValueError::CannotMutateImmutableValue.into())
    }
}

fn collect_repr(xs: &[Value], s: &mut String) {
    s.push('[');
    for (i, v) in xs.iter().enumerate() {
        if i != 0 {
            s.push_str(", ");
        }
        v.collect_repr(s);
    }
    s.push(']');
}

impl<'v, T: ListLike<'v>> StarlarkValue<'v> for ListGen<T>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(List::TYPE);

    fn get_methods(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.methods(crate::stdlib::list::list_methods)
    }

    fn collect_repr(&self, s: &mut String) {
        collect_repr(&*self.0.content(), s)
    }

    fn to_json(&self) -> anyhow::Result<String> {
        let mut res = String::new();
        res.push('[');
        for (i, e) in self.0.content().iter().enumerate() {
            if i != 0 {
                res.push_str(", ");
            }
            res.push_str(&e.to_json()?);
        }
        res.push(']');
        Ok(res)
    }

    fn to_bool(&self) -> bool {
        !self.0.content().is_empty()
    }

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match List::from_value(other) {
            None => Ok(false),
            Some(other) => equals_slice(&*self.0.content(), &other.content, |x, y| x.equals(*y)),
        }
    }

    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        match List::from_value(other) {
            None => ValueError::unsupported_with(self, "cmp()", other),
            Some(other) => compare_slice(&*self.0.content(), &other.content, |x, y| x.compare(*y)),
        }
    }

    fn at(&self, index: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let i = convert_index(index, self.0.content().len() as i32)? as usize;
        Ok(self.0.content()[i])
    }

    fn extra_memory(&self) -> usize {
        self.0.content().capacity() * mem::size_of::<Value>()
    }

    fn length(&self) -> anyhow::Result<i32> {
        Ok(self.0.content().len() as i32)
    }

    fn is_in(&self, other: Value<'v>) -> anyhow::Result<bool> {
        for x in self.0.content().iter() {
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
        let xs = self.0.content();
        let res = apply_slice(&*xs, start, stop, stride)?;
        Ok(heap.alloc(List::new(res)))
    }

    fn iterate<'a>(
        &'a self,
        _heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'a>>
    where
        'v: 'a,
    {
        Ok(box ARefIterator::new(self.0.content(), |x| {
            x.iter().copied()
        }))
    }

    fn with_iterator(
        &self,
        _heap: &'v Heap,
        f: &mut dyn FnMut(&mut dyn Iterator<Item = Value<'v>>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        f(&mut self.0.content().iter().copied())
    }

    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = List::from_value(other) {
            let mut result = Vec::with_capacity(self.0.content().len() + other.len());
            result.extend(self.0.content().iter());
            result.extend(other.iter());
            Ok(heap.alloc(List::new(result)))
        } else {
            ValueError::unsupported_with(self, "+", other)
        }
    }

    fn mul(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_int() {
            Some(l) => {
                let mut result =
                    Vec::with_capacity(self.0.content().len() * cmp::max(0, l) as usize);
                for _ in 0..l {
                    result.extend(self.0.content().iter());
                }
                Ok(heap.alloc(List::new(result)))
            }
            None => Err(ValueError::IncorrectParameterType.into()),
        }
    }

    fn set_at(&self, index: Value<'v>, alloc_value: Value<'v>) -> anyhow::Result<()> {
        let i = convert_index(index, self.0.content().len() as i32)? as usize;
        self.0.set_at(i, alloc_value)
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
