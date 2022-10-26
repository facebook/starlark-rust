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

use gazebo::prelude::*;

use crate::iter::def_double_ended_iter;
use crate::iter::def_iter;
use crate::vec_map;

/// Iterator over a small map entry references.
#[derive(Clone_)]
pub struct Iter<'a, K, V> {
    pub(crate) iter: vec_map::Iter<'a, K, V>,
}

impl<'a, K, V> Iter<'a, K, V> {
    #[inline]
    fn map((k, v): (&'a K, &'a V)) -> <Self as Iterator>::Item {
        (k, v)
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    def_iter!();
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    def_double_ended_iter!();
}

/// Iterator over a small map mutable entry references.
pub struct IterMut<'a, K, V> {
    pub(crate) iter: vec_map::IterMut<'a, K, V>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    #[inline]
    fn map((k, v): (&'a K, &'a mut V)) -> <Self as Iterator>::Item {
        (k, v)
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    def_iter!();
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    def_double_ended_iter!();
}

/// Iterator over a small map entries.
pub struct IntoIter<K, V> {
    pub(crate) iter: vec_map::IntoIter<K, V>,
}

impl<K, V> IntoIter<K, V> {
    #[inline]
    fn map((k, v): (K, V)) -> <Self as Iterator>::Item {
        (k, v)
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    def_iter!();
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    def_double_ended_iter!();
}

fn _assert_iterators_sync_send() {
    fn assert_sync_send<T: Sync + Send>(_: T) {}
    fn test_iter(iter: Iter<String, u32>) {
        assert_sync_send(iter);
    }
    fn test_into_iter(iter: IntoIter<String, u32>) {
        assert_sync_send(iter);
    }
}
