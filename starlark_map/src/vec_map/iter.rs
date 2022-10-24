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

use gazebo::prelude::Clone_;

use crate::iter::def_double_ended_iter;
use crate::iter::def_iter;
use crate::vec_map::Bucket;
use crate::Hashed;

#[derive(Clone_)]
pub(crate) struct Keys<'a, K: 'a, V: 'a> {
    pub(crate) iter: std::slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K: 'a, V: 'a> Keys<'a, K, V> {
    #[inline]
    fn map(b: &'a Bucket<K, V>) -> <Self as Iterator>::Item {
        &b.key
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Keys<'a, K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Keys<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

#[derive(Clone_)]
pub(crate) struct Values<'a, K: 'a, V: 'a> {
    pub(crate) iter: std::slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K: 'a, V: 'a> Values<'a, K, V> {
    #[inline]
    fn map(b: &'a Bucket<K, V>) -> <Self as Iterator>::Item {
        &b.value
    }
}

impl<'a, K: 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Values<'a, K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Values<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub(crate) struct ValuesMut<'a, K: 'a, V: 'a> {
    pub(crate) iter: std::slice::IterMut<'a, Bucket<K, V>>,
}

impl<'a, K: 'a, V: 'a> ValuesMut<'a, K, V> {
    #[inline]
    fn map(b: &'a mut Bucket<K, V>) -> <Self as Iterator>::Item {
        &mut b.value
    }
}

impl<'a, K: 'a, V: 'a> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for ValuesMut<'a, K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for ValuesMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

#[derive(Clone_)]
pub struct Iter<'a, K: 'a, V: 'a> {
    pub(crate) iter: std::slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K: 'a, V: 'a> Iter<'a, K, V> {
    #[inline]
    fn map(b: &Bucket<K, V>) -> (&K, &V) {
        (&b.key, &b.value)
    }
}

pub(crate) struct IterHash<'a, K: 'a, V: 'a> {
    pub(crate) iter: std::slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K: 'a, V: 'a> IterHash<'a, K, V> {
    #[inline]
    fn map(b: &'a Bucket<K, V>) -> (Hashed<&'a K>, &'a V) {
        (Hashed::new_unchecked(b.hash, &b.key), &b.value)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for IterHash<'a, K, V> {
    type Item = (Hashed<&'a K>, &'a V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for IterHash<'a, K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for IterHash<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    pub(crate) iter: std::slice::IterMut<'a, Bucket<K, V>>,
}

impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    #[inline]
    fn map(b: &mut Bucket<K, V>) -> (&K, &mut V) {
        (&b.key, &mut b.value)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for IterMut<'a, K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for IterMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct IntoIterHash<K, V> {
    pub(crate) iter: std::vec::IntoIter<Bucket<K, V>>,
}

impl<K, V> IntoIterHash<K, V> {
    #[inline]
    fn map(b: Bucket<K, V>) -> (Hashed<K>, V) {
        (Hashed::new_unchecked(b.hash, b.key), b.value)
    }
}

impl<K, V> Iterator for IntoIterHash<K, V> {
    type Item = (Hashed<K>, V);

    def_iter!();
}

impl<K, V> ExactSizeIterator for IntoIterHash<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<K, V> DoubleEndedIterator for IntoIterHash<K, V> {
    def_double_ended_iter!();
}

pub struct IntoIter<K, V> {
    pub(crate) iter: std::vec::IntoIter<Bucket<K, V>>,
}

impl<K, V> IntoIter<K, V> {
    #[inline]
    fn map(b: Bucket<K, V>) -> (K, V) {
        (b.key, b.value)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for IntoIter<K, V> {
    def_double_ended_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}
