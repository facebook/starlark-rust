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

//! Iterable for Starlark objects.

use crate::values::{Heap, Value};
use gazebo::cell::ARef;

/// Type to be implemented by types which are iterable.
pub trait TypedIterable<'v> {
    /// Make an iterator.
    fn to_iter<'a>(&'a self, heap: &'v Heap) -> Box<dyn Iterator<Item = Value<'v>> + 'a>
    where
        'v: 'a;
}

/// Iterable which contains borrowed reference to a sequence.
pub struct RefIterable<'v> {
    heap: &'v Heap,
    r: ARef<'v, dyn TypedIterable<'v>>,
}

impl<'v> RefIterable<'v> {
    pub fn new(heap: &'v Heap, r: ARef<'v, dyn TypedIterable<'v>>) -> Self {
        RefIterable { heap, r }
    }

    pub fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value<'v>> + 'a>
    where
        'v: 'a,
    {
        self.r.to_iter(self.heap)
    }
}

impl<'a, 'v: 'a> IntoIterator for &'a RefIterable<'v> {
    type Item = Value<'v>;

    type IntoIter = Box<dyn Iterator<Item = Value<'v>> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
