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

#![allow(dead_code)] // TODO(nga): used in the following diff.

use std::cmp::Ordering;
use std::mem;

use allocative::Allocative;
use gazebo::prelude::*;

pub(crate) mod iter;

/// Array of pairs (K, V), where K and V are stored separately.
/// This reduces memory consumption when K and V have different alignments.
#[derive(Debug, Clone, PartialEq, Eq, Default_, Hash, Allocative)]
pub(crate) struct Vec2<K, V> {
    // `keys` and `values` are always the same length.
    keys: Vec<K>,
    values: Vec<V>,
}

impl<K, V> Vec2<K, V> {
    pub(crate) const fn new() -> Vec2<K, V> {
        Vec2 {
            keys: Vec::new(),
            values: Vec::new(),
        }
    }

    pub(crate) fn with_capacity(capacity: usize) -> Vec2<K, V> {
        Vec2 {
            keys: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.keys.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    pub(crate) fn capacity(&self) -> usize {
        self.keys.capacity()
    }

    pub(crate) fn reserve(&mut self, additional: usize) {
        self.keys.reserve(additional);
        self.values.reserve(additional);
    }

    pub(crate) fn get(&self, index: usize) -> Option<(&K, &V)> {
        Some((self.keys.get(index)?, self.values.get(index)?))
    }

    pub(crate) unsafe fn get_unchecked(&self, index: usize) -> (&K, &V) {
        (
            self.keys.get_unchecked(index),
            self.values.get_unchecked(index),
        )
    }

    pub(crate) unsafe fn get_unchecked_mut(&mut self, index: usize) -> (&mut K, &mut V) {
        (
            self.keys.get_unchecked_mut(index),
            self.values.get_unchecked_mut(index),
        )
    }

    pub(crate) fn push(&mut self, key: K, value: V) {
        self.keys.push(key);
        self.values.push(value);
    }

    pub(crate) fn remove(&mut self, index: usize) -> (K, V) {
        (self.keys.remove(index), self.values.remove(index))
    }

    pub(crate) fn clear(&mut self) {
        self.keys.clear();
        self.values.clear();
    }

    pub(crate) fn pop(&mut self) -> Option<(K, V)> {
        let key = self.keys.pop()?;
        let value = self.values.pop()?;
        Some((key, value))
    }

    pub(crate) fn iter(&self) -> iter::Iter<'_, K, V> {
        iter::Iter {
            keys: self.keys.iter(),
            values: self.values.iter(),
        }
    }

    pub(crate) fn into_iter(self) -> iter::IntoIter<K, V> {
        iter::IntoIter {
            keys: self.keys.into_iter(),
            values: self.values.into_iter(),
        }
    }

    pub(crate) fn keys(&self) -> &[K] {
        &self.keys
    }

    pub(crate) fn keys_mut(&mut self) -> &mut [K] {
        &mut self.keys
    }

    pub(crate) fn values(&self) -> &[V] {
        &self.values
    }

    pub(crate) fn sort_by<F>(&mut self, mut compare: F)
    where
        F: FnMut((&K, &V), (&K, &V)) -> Ordering,
    {
        // TODO: sort without allocation.
        // TODO: drain.
        let mut entries: Vec<(K, V)> = mem::take(self).into_iter().collect();
        entries.sort_by(|(ak, av), (bk, bv)| compare((ak, av), (bk, bv)));
        for (k, v) in entries {
            self.push(k, v);
        }
    }
}

impl<'a, K, V> IntoIterator for &'a Vec2<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = iter::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {}
}
