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

use crate::collections::hash::{BorrowHashed, Hashed, SmallHashResult};
use gazebo::prelude::*;
use indexmap::{Equivalent, IndexMap};
use std::{fmt, hash::BuildHasher, mem};

// TODO: benchmark, is this the right threshold
const THRESHOLD: usize = 12;

// We define a lot of iterators on top of other iterators
// so define a helper macro for that
macro_rules! def_iter {
    () => {
        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map(Self::map)
        }

        fn nth(&mut self, n: usize) -> Option<Self::Item> {
            self.iter.nth(n).map(Self::map)
        }

        fn last(mut self) -> Option<Self::Item> {
            // Since these are all double-ended iterators we can skip to the end quickly
            self.iter.next_back().map(Self::map)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            self.iter.size_hint()
        }

        fn count(self) -> usize {
            self.iter.len()
        }

        fn collect<C>(self) -> C
        where
            C: std::iter::FromIterator<Self::Item>,
        {
            self.iter.map(Self::map).collect()
        }
    };
}

#[derive(Debug, Clone, Eq, PartialEq, Default_)]
pub struct VecMap<K, V> {
    hashes: [SmallHashResult; THRESHOLD],
    values: Vec<(K, V)>,
}

#[derive(Clone_)]
pub struct VMKeys<'a, K: 'a, V: 'a> {
    iter: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMKeys<'a, K, V> {
    fn map(tup: &'a (K, V)) -> <Self as Iterator>::Item {
        &tup.0
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMKeys<'a, K, V> {
    type Item = &'a K;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMKeys<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

#[derive(Clone_)]
pub struct VMValues<'a, K: 'a, V: 'a> {
    iter: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMValues<'a, K, V> {
    fn map(tup: &'a (K, V)) -> <Self as Iterator>::Item {
        &tup.1
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMValues<'a, K, V> {
    type Item = &'a V;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMValues<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct VMValuesMut<'a, K: 'a, V: 'a> {
    iter: std::slice::IterMut<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMValuesMut<'a, K, V> {
    fn map(tup: &'a mut (K, V)) -> <Self as Iterator>::Item {
        &mut tup.1
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMValuesMut<'a, K, V> {
    type Item = &'a mut V;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMValuesMut<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

#[derive(Clone_)]
pub struct VMIter<'a, K: 'a, V: 'a> {
    iter: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMIter<'a, K, V> {
    fn map(tup: &(K, V)) -> (&K, &V) {
        (&tup.0, &tup.1)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMIter<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct VMIterHash<'a, K: 'a, V: 'a> {
    iter: std::iter::Zip<std::slice::Iter<'a, (K, V)>, std::slice::Iter<'a, SmallHashResult>>,
}

impl<'a, K: 'a, V: 'a> VMIterHash<'a, K, V> {
    fn map(tup: (&'a (K, V), &SmallHashResult)) -> (BorrowHashed<'a, K>, &'a V) {
        let (k, v) = tup.0;
        let h = tup.1;
        (BorrowHashed::new_unchecked(*h, k), v)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMIterHash<'a, K, V> {
    type Item = (BorrowHashed<'a, K>, &'a V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMIterHash<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct VMIterMut<'a, K: 'a, V: 'a> {
    iter: std::slice::IterMut<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMIterMut<'a, K, V> {
    fn map(tup: &mut (K, V)) -> (&K, &mut V) {
        (&tup.0, &mut tup.1)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMIterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct VMIntoIterHash<K, V> {
    // We'd love to make a single iterator, but it's currently impossible
    // to turn a fixed array of hashes into an IntoIterator,
    // tracking it at https://github.com/rust-lang/rust/issues/25725.
    hashes: [SmallHashResult; THRESHOLD],
    iter: std::iter::Enumerate<std::vec::IntoIter<(K, V)>>,
}

impl<K, V> VMIntoIterHash<K, V> {
    // The usize is the index in self.hashes
    fn get(&self, tup: (usize, (K, V))) -> (Hashed<K>, V) {
        Self::get_hashes(&self.hashes, tup)
    }

    // The usize is the index in hashes
    fn get_hashes(hashes: &[SmallHashResult; THRESHOLD], tup: (usize, (K, V))) -> (Hashed<K>, V) {
        // The brackets below are important or rustfmt crashes,
        // see https://github.com/rust-lang/rustfmt/issues/4479
        (Hashed::new_unchecked(hashes[tup.0], (tup.1).0), (tup.1).1)
    }
}

impl<K, V> Iterator for VMIntoIterHash<K, V> {
    type Item = (Hashed<K>, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| self.get(x))
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n).map(|x| self.get(x))
    }

    fn last(mut self) -> Option<Self::Item> {
        // Since these are all double-ended iterators we can skip to the end quickly
        self.iter.next_back().map(|x| self.get(x))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn count(self) -> usize {
        self.iter.len()
    }

    fn collect<C>(self) -> C
    where
        C: std::iter::FromIterator<Self::Item>,
    {
        let hashes = self.hashes;
        self.iter.map(|x| Self::get_hashes(&hashes, x)).collect()
    }
}

impl<K, V> ExactSizeIterator for VMIntoIterHash<K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct VMIntoIter<K, V> {
    iter: std::vec::IntoIter<(K, V)>,
}

impl<K, V> VMIntoIter<K, V> {
    fn map(tup: (K, V)) -> (K, V) {
        tup
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMIntoIter<K, V> {
    type Item = (K, V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for VMIntoIter<K, V> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

pub struct InsertCapacityOverflow<K, V> {
    pub key: Hashed<K>,
    pub value: V,
}

impl<K, V> fmt::Debug for InsertCapacityOverflow<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VecMapInsertCapacityOverflow")
            // TODO(nga): use `finish_non_exhaustive` when our rust is fresh enough
            .finish()
    }
}

impl<K, V> VecMap<K, V> {
    pub fn try_with_capacity(n: usize) -> Option<Self> {
        if n <= THRESHOLD {
            Some(Self {
                hashes: [SmallHashResult::default(); THRESHOLD],
                values: Vec::with_capacity(n),
            })
        } else {
            None
        }
    }

    /// Create `VecMap` with largest capacity it can hold.
    pub fn with_largest_capacity() -> Self {
        Self {
            hashes: [SmallHashResult::default(); THRESHOLD],
            values: Vec::with_capacity(THRESHOLD),
        }
    }

    pub fn try_reserve(&mut self, additional: usize) -> bool {
        if additional > THRESHOLD.wrapping_sub(self.len()) {
            false
        } else {
            self.values.reserve(additional);
            true
        }
    }

    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }

    pub fn get_hashed<Q>(&self, key: BorrowHashed<Q>) -> Option<&V>
    where
        Q: ?Sized + Equivalent<K>,
    {
        self.get_full(key).map(|(_, _, v)| v)
    }

    pub fn get_full<Q>(&self, key: BorrowHashed<Q>) -> Option<(usize, &K, &V)>
    where
        Q: ?Sized + Equivalent<K>,
    {
        // This method is _very_ hot. There are three ways to implement this scan:
        // 1) Checked index operations.
        // 2) Unchecked index operations.
        // 3) Iterators.
        // Iterators would be best, but is significantly slower, so go with unchecked.
        // (25% on a benchmark which did a lot of other stuff too).
        debug_assert!(self.values.len() <= self.hashes.len());
        for i in 0..self.values.len() {
            // We always have at least as many hashes as value, so this index is safe.
            if unsafe { *self.hashes.get_unchecked(i) } == key.hash() {
                let v = unsafe { self.values.get_unchecked(i) };
                if key.key().equivalent(&v.0) {
                    return Some((i, &v.0, &v.1));
                }
            }
        }
        None
    }

    pub fn get_index_of_hashed<Q>(&self, key: BorrowHashed<Q>) -> Option<usize>
    where
        Q: ?Sized + Equivalent<K>,
    {
        self.get_full(key).map(|(i, _, _)| i)
    }

    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        self.values.get(index).map(|x| (&x.0, &x.1))
    }

    pub fn get_mut_hashed<Q>(&mut self, key: BorrowHashed<Q>) -> Option<&mut V>
    where
        Q: ?Sized + Equivalent<K>,
    {
        for i in 0..self.values.len() {
            if self.hashes[i] == key.hash() && key.key().equivalent(&self.values[i].0) {
                return Some(&mut self.values[i].1);
            }
        }
        None
    }

    pub fn contains_key_hashed<Q>(&self, key: BorrowHashed<Q>) -> bool
    where
        Q: Equivalent<K> + ?Sized,
    {
        for i in 0..self.values.len() {
            if self.hashes[i] == key.hash() && key.key().equivalent(&self.values[i].0) {
                return true;
            }
        }
        return false;
    }

    pub fn try_insert_hashed(
        &mut self,
        key: Hashed<K>,
        mut value: V,
    ) -> Result<Option<V>, InsertCapacityOverflow<K, V>>
    where
        K: Eq,
    {
        if let Some(v) = self.get_mut_hashed(key.borrow()) {
            mem::swap(v, &mut value);
            Ok(Some(value))
        } else if self.len() == THRESHOLD {
            Err(InsertCapacityOverflow { key, value })
        } else {
            let i = self.values.len();
            self.hashes[i] = key.hash();
            self.values.push((key.into_key(), value));
            Ok(None)
        }
    }

    pub fn remove_hashed_entry<Q>(&mut self, key: BorrowHashed<Q>) -> Option<(K, V)>
    where
        Q: ?Sized + Equivalent<K>,
    {
        let len = self.values.len();
        if len == 0 {
            return None;
        }

        for i in 0..len {
            if self.hashes[i] == key.hash() && key.key().equivalent(&self.values[i].0) {
                for j in i..len - 1 {
                    self.hashes[j] = self.hashes[j + 1];
                }
                return Some(self.values.remove(i));
            }
        }
        None
    }

    pub fn remove_hashed<Q>(&mut self, key: BorrowHashed<Q>) -> Option<V>
    where
        Q: ?Sized + Equivalent<K>,
    {
        self.remove_hashed_entry(key).map(|(_, v)| v)
    }

    pub fn entry_hashed(&mut self, key: Hashed<K>) -> Entry<'_, K, V>
    where
        K: Eq,
    {
        // We could use `get_mut_hashed` here, but because of borrow checker limitations
        // we can't, so we do copy-paste.
        for i in 0..self.values.len() {
            if self.hashes[i] == key.hash() && key.key().equivalent(&self.values[i].0) {
                return Entry::Occupied(OccupiedEntry {
                    key,
                    value: &mut self.values[i].1,
                });
            }
        }

        if self.len() == THRESHOLD {
            Entry::VacantFull(VacantFullEntry { key })
        } else {
            Entry::Vacant(VacantEntry { key, map: self })
        }
    }

    pub fn drain_to<S>(&mut self, map: &mut IndexMap<Hashed<K>, V, S>)
    where
        K: Eq,
        S: BuildHasher + Default,
    {
        let hashes = &self.hashes;
        let values = &mut self.values;

        map.extend(
            values
                .drain(..)
                .enumerate()
                .map(|(i, p)| (Hashed::new_unchecked(hashes[i], p.0), p.1)),
        );
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn values(&self) -> VMValues<K, V> {
        VMValues {
            iter: self.values.iter(),
        }
    }

    pub fn values_mut(&mut self) -> VMValuesMut<K, V> {
        VMValuesMut {
            iter: self.values.iter_mut(),
        }
    }

    pub fn keys(&self) -> VMKeys<K, V> {
        VMKeys {
            iter: self.values.iter(),
        }
    }

    pub fn into_iter(self) -> VMIntoIter<K, V> {
        VMIntoIter {
            iter: self.values.into_iter(),
        }
    }

    pub fn iter(&self) -> VMIter<K, V> {
        VMIter {
            iter: self.values.iter(),
        }
    }

    pub fn iter_hashed(&self) -> VMIterHash<K, V> {
        VMIterHash {
            // Values go first since they terminate first and we can short-circuit
            iter: self.values.iter().zip(self.hashes.iter()),
        }
    }

    pub fn into_iter_hashed(self) -> VMIntoIterHash<K, V> {
        // See the comments on VMIntoIterHash for why this one looks different
        VMIntoIterHash {
            hashes: self.hashes,
            iter: self.values.into_iter().enumerate(),
        }
    }

    pub fn iter_mut(&mut self) -> VMIterMut<K, V> {
        VMIterMut {
            iter: self.values.iter_mut(),
        }
    }
}

/// Occupied entry for the given key.
pub struct OccupiedEntry<'a, K, V> {
    key: Hashed<K>,
    value: &'a mut V,
}

/// Empty entry for the given key.
pub struct VacantEntry<'a, K, V> {
    key: Hashed<K>,
    map: &'a mut VecMap<K, V>,
}

/// Value not found by the key, but the [`VecMap`] is at full capacity,
/// so the vacant entry cannot be updated.
pub struct VacantFullEntry<K> {
    key: Hashed<K>,
}

/// [`VecMap`] entry.
pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
    VacantFull(VacantFullEntry<K>),
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        self.key.key()
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.value
    }

    pub fn get(&self) -> &V {
        self.value
    }
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        self.key.key()
    }

    pub fn insert(self, value: V) -> &'a mut V {
        let i = self.map.values.len();
        self.map.hashes[i] = self.key.hash();
        self.map.values.push((self.key.into_key(), value));
        &mut self.map.values.last_mut().unwrap().1
    }
}

impl<K> VacantFullEntry<K> {
    pub fn key(&self) -> &K {
        self.key.key()
    }

    pub fn into_hashed_key(self) -> Hashed<K> {
        self.key
    }
}

impl<'a, K, V> Entry<'a, K, V> {
    #[allow(dead_code)]
    pub fn _key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
            Entry::VacantFull(e) => e.key(),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::collections::{
        vec_map::{Entry, VecMap, THRESHOLD},
        Hashed,
    };

    #[test]
    fn entry() {
        let mut m: VecMap<u32, u64> = VecMap::default();

        let e = m.entry_hashed(Hashed::new(10));
        let e = match e {
            Entry::Vacant(e) => e,
            _ => panic!(),
        };
        assert_eq!(&10, e.key());

        assert_eq!(&mut 100, e.insert(100));

        let e = m.entry_hashed(Hashed::new(10));
        let mut e = match e {
            Entry::Occupied(e) => e,
            _ => panic!(),
        };

        assert_eq!(&100, e.get());
        assert_eq!(&mut 100, e.get_mut());
    }

    #[test]
    fn try_reserve() {
        let mut v: VecMap<u32, u64> = VecMap::default();
        assert!(v.try_reserve(1));
        assert!(v.try_reserve(THRESHOLD));
        assert!(!v.try_reserve(THRESHOLD + 1));
        assert!(!v.try_reserve(isize::max_value() as usize));
        assert!(!v.try_reserve(usize::max_value()));

        v.try_insert_hashed(Hashed::new(10), 100).unwrap();
        v.try_insert_hashed(Hashed::new(20), 200).unwrap();
        assert!(v.try_reserve(1));
        assert!(v.try_reserve(THRESHOLD - 2));
        assert!(!v.try_reserve(THRESHOLD - 1));
        assert!(!v.try_reserve(isize::max_value() as usize));
        assert!(!v.try_reserve(usize::max_value()));
    }
}
