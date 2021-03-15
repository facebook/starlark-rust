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

//! Define the list type of Starlark
use crate::{
    environment::{Globals, GlobalsStatic},
    values::{
        comparison::{compare_slice, equals_slice},
        error::ValueError,
        index::{convert_index, convert_slice_indices},
        iter::TypedIterable,
        tuple, unsupported_with, AllocFrozenValue, AllocValue, Freezer, FrozenHeap, FrozenValue,
        Heap, ImmutableValue, MutableValue, TypedValue, Value, ValueLike, Walker,
    },
};
use gazebo::{any::AnyLifetime, cell::ARef, prelude::*};
use std::cmp::Ordering;

#[derive(Clone, Default_, Debug)]
pub struct ListGen<T> {
    pub content: Vec<T>,
}

impl<T> ListGen<T> {
    pub const TYPE: &'static str = "list";
}

starlark_value!(pub List);

impl<'v, T: AllocValue<'v>> AllocValue<'v> for Vec<T> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_mutable(List {
            content: self.into_map(|x| x.alloc_value(heap)),
        })
    }
}

impl<'v, T: AllocFrozenValue<'v>> AllocFrozenValue<'v> for Vec<T> {
    fn alloc_frozen_value(self, heap: &'v FrozenHeap) -> FrozenValue {
        heap.alloc_immutable(FrozenList {
            content: self.into_map(|x| x.alloc_frozen_value(heap)),
        })
    }
}

impl FrozenList {
    // We need a lifetime because FrozenValue doesn't contain the right lifetime
    #[allow(clippy::trivially_copy_pass_by_ref)]
    pub fn from_value(x: &FrozenValue) -> Option<ARef<FrozenList>> {
        x.downcast_ref::<FrozenList>()
    }
}

impl<'v> MutableValue<'v> for List<'v> {
    fn freeze<'fv>(self: Box<Self>, freezer: &'fv Freezer) -> Box<dyn ImmutableValue<'fv> + 'fv> {
        let mut content = Vec::with_capacity(self.content.len());
        for v in self.content {
            content.push(v.freeze(freezer))
        }
        box FrozenList { content }
    }

    fn walk(&mut self, walker: &Walker<'v>) {
        self.content.iter_mut().for_each(|x| walker.walk(x))
    }
}

impl<'v> ImmutableValue<'v> for FrozenList {
    fn thaw(&self, heap: &'v Heap) -> Box<dyn MutableValue<'v> + 'v> {
        let vals = self.content.map(|e| heap.alloc_thaw_on_write(*e));
        box List { content: vals }
    }
}

impl<'v, T: ValueLike<'v>> ListGen<T> {
    pub fn new(content: Vec<T>) -> Self {
        Self { content }
    }

    pub fn len(&self) -> usize {
        self.content.len()
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = Value<'v>> + 'a
    where
        'v: 'a,
    {
        self.content.iter().map(|e| e.to_value())
    }
}

impl<'v> List<'v> {
    pub fn push(&mut self, value: Value<'v>) {
        self.content.push(value);
    }

    pub fn extend(&mut self, other: Vec<Value<'v>>) {
        self.content.extend(other);
    }

    pub fn clear(&mut self) {
        self.content.clear();
    }

    pub fn insert(&mut self, index: usize, value: Value<'v>) {
        self.content.insert(index, value);
    }

    pub fn pop(&mut self, index: i32) -> anyhow::Result<Value<'v>> {
        if index < 0 || index >= self.content.len() as i32 {
            return Err(ValueError::IndexOutOfBound(index).into());
        }
        Ok(self.content.remove(index as usize))
    }

    pub fn position(&self, needle: Value<'v>) -> Option<usize> {
        self.content.iter().position(|v| v == &needle)
    }

    pub fn remove(&mut self, position: usize) {
        self.content.remove(position);
    }
}

impl<'v, T: ValueLike<'v>> TypedValue<'v> for ListGen<T>
where
    Self: MutableList<'v> + AnyLifetime<'v>,
{
    starlark_type!(List::TYPE);

    fn naturally_mutable(&self) -> bool {
        true
    }

    fn get_members(&self) -> Option<&'static Globals> {
        static RES: GlobalsStatic = GlobalsStatic::new();
        RES.members(crate::stdlib::list::list_members)
    }

    /// Returns a string representation for the list
    ///
    /// # Examples:
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// repr([1,2,3]) == '[1, 2, 3]'
    /// repr([1,[2,3]]) == '[1, [2, 3]]'
    /// repr([1]) == '[1]'
    /// repr([]) == '[]'
    /// # "#);
    /// ```
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

    fn to_json(&self) -> String {
        format!(
            "[{}]",
            self.content.iter().map(|e| e.to_json()).enumerate().fold(
                "".to_string(),
                |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + "," + &s.1
                },
            )
        )
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
            None => unsupported_with(self, "cmp()", other),
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

    fn iterate(&self) -> anyhow::Result<&(dyn TypedIterable<'v> + 'v)> {
        Ok(self)
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a list.
    ///
    /// # Example
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// [1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
    /// # "#);
    /// ```
    fn add(&self, _original: Value, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = List::from_value(other) {
            let mut result = List {
                content: Vec::new(),
            };
            for x in &self.content {
                result.content.push(x.to_value());
            }
            for x in other.iter() {
                result.content.push(x);
            }
            Ok(heap.alloc(result))
        } else {
            unsupported_with(self, "+", other)
        }
    }

    fn add_assign(
        &self,
        lhs: Value<'v>,
        other: Value<'v>,
    ) -> anyhow::Result<Box<dyn FnOnce(&'v Heap) -> anyhow::Result<()> + 'v>> {
        // This API isn't beautiful :-(
        //
        // We need to have a &self to do dynamic dispatch. That requires us borrowing the value.
        // We can borrow self mutably, but then if other is the same value, we can't access that.
        // We can borrow self immutably, but then we need to upgrade it to mutable to do the actual write,
        // and before doing that write, we need to drop the immutable borrow.
        //
        // This API does that magic. Borrow immutably, so we can dispatch to the right instance.
        // Then return a function which runs after the borrow, and that can reconvert to a mutable borrow
        // and operate on it.
        if let Some(other) = List::from_value(other) {
            // Important we have finished using other, so that we can have exclusive access for content_mut
            let items = other.iter().collect::<Vec<_>>();
            Ok(box move |heap| {
                List::from_value_mut(lhs, heap)?.unwrap().extend(items);
                Ok(())
            })
        } else {
            unsupported_with(self, "+=", other)
        }
    }

    /// Repeat `other` times this tuple.
    ///
    /// `other` has to be an int or a boolean.
    ///
    /// # Example
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// [1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
    /// # "#);
    /// ```
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

    /// Set the value at `index` to `alloc_value`
    ///
    /// # Example
    /// ```rust
    /// # starlark::assert::is_true(r#"
    /// v = [1, 2, 3]
    /// v[1] = 1
    /// v[2] = [2,3]
    /// v == [1, 1, [2, 3]]
    /// # "#);
    /// ```
    fn set_at(&mut self, index: Value<'v>, alloc_value: Value<'v>) -> anyhow::Result<()> {
        let i = convert_index(index, self.len() as i32)? as usize;
        self.mutable_list().content[i] = alloc_value;
        Ok(())
    }
}

impl<'v, T: ValueLike<'v>> TypedIterable<'v> for ListGen<T> {
    fn to_iter<'a>(&'a self, _heap: &'v Heap) -> Box<dyn Iterator<Item = Value<'v>> + 'a>
    where
        'v: 'a,
    {
        box self.iter()
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
