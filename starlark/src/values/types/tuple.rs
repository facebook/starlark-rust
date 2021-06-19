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

//! The list type, an immutable sequence of values.

use crate::values::{
    comparison::{compare_slice, equals_slice},
    index::{convert_index, convert_slice_indices},
    AllocValue, ComplexValue, Freezer, Heap, SimpleValue, StarlarkIterable, StarlarkValue,
    UnpackValue, Value, ValueError, ValueLike, Walker,
};
use gazebo::{any::AnyLifetime, prelude::*};
use std::{cmp::Ordering, collections::hash_map::DefaultHasher, hash::Hasher};

/// Used by both list and tuple to implement the slice function
pub(crate) fn slice_vector<'a, 'v, V: ValueLike<'v> + 'a, I: Iterator<Item = &'a V>>(
    start: i32,
    stop: i32,
    stride: i32,
    content: I,
) -> Vec<Value<'v>> {
    let (low, take, astride) = if stride < 0 {
        (stop + 1, start - stop, -stride)
    } else {
        (start, stop - start, stride)
    };
    if take <= 0 {
        return Vec::new();
    }
    let mut v: Vec<Value> = content
        .skip(low as usize)
        .take(take as usize)
        .map(|e| e.to_value())
        .collect();
    if stride < 0 {
        v.reverse();
    }
    v.into_iter()
        .enumerate()
        .filter_map(|x| {
            if 0 == (x.0 as i32 % astride) {
                Some(x.1)
            } else {
                None
            }
        })
        .collect()
}

/// Define the tuple type. See [`Tuple`] and [`FrozenTuple`] as the two aliases.
#[derive(Clone, Default_, Debug)]
pub struct TupleGen<V> {
    /// The data stored by the tuple.
    pub content: Vec<V>,
}

starlark_complex_value!(pub Tuple);

impl<'v, V: ValueLike<'v>> TupleGen<V> {
    /// Create a new tuple.
    pub fn new(content: Vec<V>) -> Self {
        Self { content }
    }

    /// Get the length of the tuple.
    pub fn len(&self) -> usize {
        self.content.len()
    }

    /// Iterate over the elements of the tuple.
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = Value<'v>> + 'a
    where
        'v: 'a,
    {
        self.content.iter().map(|e| e.to_value())
    }
}

impl<'v> ComplexValue<'v> for Tuple<'v> {
    fn freeze(self: Box<Self>, freezer: &Freezer) -> anyhow::Result<Box<dyn SimpleValue>> {
        let mut frozen = Vec::with_capacity(self.content.len());
        for v in self.content {
            frozen.push(v.freeze(freezer)?)
        }
        Ok(box FrozenTuple { content: frozen })
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        self.content.iter_mut().for_each(|x| walker.walk(x))
    }
}

impl<V> TupleGen<V> {
    pub const TYPE: &'static str = "tuple";
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for TupleGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(Tuple::TYPE);

    fn collect_repr(&self, s: &mut String) {
        s.push('(');
        let mut first = true;
        for v in &self.content {
            if first {
                first = false;
            } else {
                s.push_str(", ");
            }
            v.collect_repr(s);
        }

        if self.content.len() == 1 {
            s.push(',');
        }
        s.push(')');
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }
    fn get_hash(&self) -> anyhow::Result<u64> {
        let mut s = DefaultHasher::new();
        for v in self.content.iter() {
            s.write_u64(v.get_hash()?)
        }
        Ok(s.finish())
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

    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        match Tuple::from_value(other) {
            None => Ok(false),
            Some(other) => equals_slice(&self.content, &other.content, |x, y| x.equals(*y)),
        }
    }

    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        match Tuple::from_value(other) {
            None => ValueError::unsupported_with(self, "cmp()", other),
            Some(other) => compare_slice(&self.content, &other.content, |x, y| x.compare(*y)),
        }
    }

    fn at(&self, index: Value, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        let i = convert_index(index, self.content.len() as i32)? as usize;
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
        let (start, stop, stride) =
            convert_slice_indices(self.content.len() as i32, start, stop, stride)?;
        Ok(heap.alloc(Tuple::new(slice_vector(
            start,
            stop,
            stride,
            self.content.iter(),
        ))))
    }

    fn iterate(&self) -> anyhow::Result<&(dyn StarlarkIterable<'v> + 'v)> {
        Ok(self)
    }

    fn add(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(other) = Tuple::from_value(other) {
            let mut result = Tuple {
                content: Vec::with_capacity(self.content.len() + other.len()),
            };
            for x in self.iter() {
                result.content.push(x);
            }
            for x in other.iter() {
                result.content.push(x);
            }
            Ok(heap.alloc(result))
        } else {
            ValueError::unsupported_with(self, "a", other)
        }
    }

    fn mul(&self, other: Value, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match other.unpack_int() {
            Some(l) => {
                let mut result = Tuple {
                    content: Vec::new(),
                };
                for _i in 0..l {
                    result
                        .content
                        .extend(self.content.iter().map(|e| e.to_value()));
                }
                Ok(heap.alloc(result))
            }
            None => Err(ValueError::IncorrectParameterType.into()),
        }
    }
}

impl<'v, V: ValueLike<'v> + 'v> StarlarkIterable<'v> for TupleGen<V> {
    fn to_iter<'a>(&'a self, _heap: &'v Heap) -> Box<dyn Iterator<Item = Value<'v>> + 'a>
    where
        'v: 'a,
    {
        box self.iter()
    }
}

impl<'v, T1: AllocValue<'v>> AllocValue<'v> for (T1,) {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc(Tuple {
            content: vec![self.0.alloc_value(heap)],
        })
    }
}

impl<'v, T1: AllocValue<'v>, T2: AllocValue<'v>> AllocValue<'v> for (T1, T2) {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc(Tuple {
            content: vec![self.0.alloc_value(heap), self.1.alloc_value(heap)],
        })
    }
}

impl<'v, T1: AllocValue<'v>, T2: AllocValue<'v>, T3: AllocValue<'v>> AllocValue<'v>
    for (T1, T2, T3)
{
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc(Tuple {
            content: vec![
                self.0.alloc_value(heap),
                self.1.alloc_value(heap),
                self.2.alloc_value(heap),
            ],
        })
    }
}

impl<'v, T1: UnpackValue<'v>, T2: UnpackValue<'v>> UnpackValue<'v> for (T1, T2) {
    fn unpack_value(value: Value<'v>) -> Option<Self> {
        let t = Tuple::from_value(value)?;
        if t.len() != 2 {
            return None;
        }
        Some((
            T1::unpack_value(t.content[0])?,
            T2::unpack_value(t.content[1])?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_to_str() {
        assert::all_true(
            r#"
str((1, 2, 3)) == "(1, 2, 3)"
str((1, (2, 3))) == "(1, (2, 3))"
str((1,)) == "(1,)"
"#,
        );
    }
}
