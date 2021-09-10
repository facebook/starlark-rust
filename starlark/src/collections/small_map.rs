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

//! A Map with deterministic iteration order that specializes its storage based on the number of
//! entries to optimize memory. The Map uses a vector backed storage for few number of entries
//! and the ['IndexMap'](IndexMap) crate for larger number of entries
//!

use crate::collections::{
    hash::{BorrowHashed, Hashed},
    idhasher::BuildIdHasher,
    vec_map,
    vec_map::{
        VMIntoIter, VMIntoIterHash, VMIter, VMIterHash, VMIterMut, VMKeys, VMValues, VMValuesMut,
        VecMap,
    },
};
use gazebo::{
    coerce::{Coerce, CoerceKey},
    prelude::*,
};
use indexmap::{Equivalent, IndexMap};
use std::{
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    iter::FromIterator,
    mem,
};

#[derive(Debug, Clone)]
#[repr(C)]
enum MapHolder<K, V> {
    // As of indexmap-1.6 and THRESHOLD=12 both VecMap and IndexMap take 9 words

    // TODO: benchmark
    // We could use Vec(VecMap) for empty values, but then creating an empty
    // value would require initialising a full VecMap.
    // On the flip side, we'd simplify the branches and iterators.
    Empty,
    Vec(VecMap<K, V>),
    // We use a custom hasher since we are only ever hashing a 32bit
    // hash, so can use something faster than the default hasher.
    Map(IndexMap<Hashed<K>, V, BuildIdHasher>),
}

// We define a lot of iterators on top of three other iterators
// so define a helper macro for that
macro_rules! def_iter {
    () => {
        fn next(&mut self) -> Option<Self::Item> {
            match self {
                Self::Empty => None,
                Self::Vec(iter) => iter.next(),
                Self::Map(iter) => iter.next().map(Self::map),
            }
        }

        fn nth(&mut self, n: usize) -> Option<Self::Item> {
            match self {
                Self::Empty => None,
                Self::Vec(iter) => iter.nth(n),
                Self::Map(iter) => iter.nth(n).map(Self::map),
            }
        }

        fn last(self) -> Option<Self::Item> {
            match self {
                Self::Empty => None,
                Self::Vec(iter) => iter.last(),
                Self::Map(iter) => iter.last().map(Self::map),
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            match self {
                Self::Empty => (0, Some(0)),
                Self::Vec(iter) => iter.size_hint(),
                Self::Map(iter) => iter.size_hint(),
            }
        }

        fn count(self) -> usize {
            match self {
                Self::Empty => 0,
                Self::Vec(iter) => iter.count(),
                Self::Map(iter) => iter.count(),
            }
        }

        fn collect<C>(self) -> C
        where
            C: std::iter::FromIterator<Self::Item>,
        {
            match self {
                Self::Empty => C::from_iter(None),
                Self::Vec(iter) => iter.collect(),
                Self::Map(iter) => iter.map(Self::map).collect(),
            }
        }
    };
}

macro_rules! def_exact_size_iter {
    () => {
        fn len(&self) -> usize {
            match self {
                Self::Empty => 0,
                Self::Vec(iter) => iter.len(),
                Self::Map(iter) => iter.len(),
            }
        }
    };
}

#[derive(Clone_)]
enum MHKeys<'a, K: 'a, V: 'a> {
    Empty,
    Vec(VMKeys<'a, K, V>),
    Map(indexmap::map::Keys<'a, Hashed<K>, V>),
}

impl<'a, K: 'a, V: 'a> MHKeys<'a, K, V> {
    fn map(x: &Hashed<K>) -> &K {
        x.key()
    }
}

impl<'a, K: 'a, V: 'a> Iterator for MHKeys<'a, K, V> {
    type Item = &'a K;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for MHKeys<'a, K, V> {
    def_exact_size_iter!();
}

#[derive(Clone_)]
enum MHValues<'a, K: 'a, V: 'a> {
    Empty,
    Vec(VMValues<'a, K, V>),
    Map(indexmap::map::Values<'a, Hashed<K>, V>),
}

impl<'a, K: 'a, V: 'a> MHValues<'a, K, V> {
    fn map(x: &V) -> &V {
        x
    }
}

impl<'a, K: 'a, V: 'a> Iterator for MHValues<'a, K, V> {
    type Item = &'a V;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for MHValues<'a, K, V> {
    def_exact_size_iter!();
}

enum MHValuesMut<'a, K: 'a, V: 'a> {
    Empty,
    Vec(VMValuesMut<'a, K, V>),
    Map(indexmap::map::ValuesMut<'a, Hashed<K>, V>),
}

impl<'a, K: 'a, V: 'a> MHValuesMut<'a, K, V> {
    fn map(x: &mut V) -> &mut V {
        x
    }
}

impl<'a, K: 'a, V: 'a> Iterator for MHValuesMut<'a, K, V> {
    type Item = &'a mut V;

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for MHValuesMut<'a, K, V> {
    def_exact_size_iter!();
}

#[derive(Clone_)]
pub enum MHIter<'a, K: 'a, V: 'a> {
    Empty,
    Vec(VMIter<'a, K, V>),
    Map(indexmap::map::Iter<'a, Hashed<K>, V>),
}

impl<'a, K: 'a, V: 'a> MHIter<'a, K, V> {
    fn map(x: (&'a Hashed<K>, &'a V)) -> (&'a K, &'a V) {
        (x.0.key(), x.1)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for MHIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for MHIter<'a, K, V> {
    def_exact_size_iter!();
}

enum MHIterHash<'a, K: 'a, V: 'a> {
    Empty,
    Vec(VMIterHash<'a, K, V>),
    Map(indexmap::map::Iter<'a, Hashed<K>, V>),
}

impl<'a, K: 'a, V: 'a> MHIterHash<'a, K, V> {
    fn map(x: (&'a Hashed<K>, &'a V)) -> (BorrowHashed<'a, K>, &'a V) {
        (x.0.borrow(), x.1)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for MHIterHash<'a, K, V> {
    type Item = (BorrowHashed<'a, K>, &'a V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for MHIterHash<'a, K, V> {
    def_exact_size_iter!();
}

enum MHIntoIterHash<K, V> {
    Empty,
    Vec(VMIntoIterHash<K, V>),
    Map(indexmap::map::IntoIter<Hashed<K>, V>),
}

impl<K, V> MHIntoIterHash<K, V> {
    fn map(x: (Hashed<K>, V)) -> (Hashed<K>, V) {
        x
    }
}

impl<K, V> Iterator for MHIntoIterHash<K, V> {
    type Item = (Hashed<K>, V);

    def_iter!();
}

impl<K, V> ExactSizeIterator for MHIntoIterHash<K, V> {
    def_exact_size_iter!();
}

pub enum MHIterMut<'a, K: 'a, V: 'a> {
    Empty,
    Vec(VMIterMut<'a, K, V>),
    Map(indexmap::map::IterMut<'a, Hashed<K>, V>),
}

impl<'a, K: 'a, V: 'a> MHIterMut<'a, K, V> {
    fn map(x: (&'a Hashed<K>, &'a mut V)) -> (&'a K, &'a mut V) {
        (x.0.key(), x.1)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for MHIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    def_iter!();
}

impl<'a, K: 'a, V: 'a> ExactSizeIterator for MHIterMut<'a, K, V> {
    def_exact_size_iter!();
}

pub enum MHIntoIter<K, V> {
    Empty,
    Vec(VMIntoIter<K, V>),
    Map(indexmap::map::IntoIter<Hashed<K>, V>),
}

impl<K, V> MHIntoIter<K, V> {
    fn map(x: (Hashed<K>, V)) -> (K, V) {
        (x.0.into_key(), x.1)
    }
}

impl<K, V> Iterator for MHIntoIter<K, V> {
    type Item = (K, V);

    def_iter!();
}

impl<K, V> ExactSizeIterator for MHIntoIter<K, V> {
    def_exact_size_iter!();
}

impl<K, V> MapHolder<K, V> {
    fn with_capacity(n: usize) -> Self {
        if n == 0 {
            MapHolder::Empty
        } else {
            match VecMap::try_with_capacity(n) {
                Some(vec) => MapHolder::Vec(vec),
                None => MapHolder::Map(IndexMap::with_capacity_and_hasher(n, Default::default())),
            }
        }
    }

    fn with_capacity_largest_vec() -> Self {
        MapHolder::Vec(VecMap::with_largest_capacity())
    }
}

impl<K, V> Default for MapHolder<K, V> {
    fn default() -> Self {
        MapHolder::Empty
    }
}

/// An memory-efficient key-value map with determinstic order.
///
/// Provides the standard container operations, modelled most closely on [`IndexMap`](indexmap::IndexMap), plus:
///
/// * Variants which take an already hashed value, e.g. [`get_hashed`](SmallMap::get_hashed).
///
/// * Functions which work with the position, e.g. [`get_index_of`](SmallMap::get_index_of).
#[repr(C)]
#[derive(Clone, Default_)]
pub struct SmallMap<K, V> {
    state: MapHolder<K, V>,
}

unsafe impl<FromK, FromV, ToK, ToV> Coerce<SmallMap<ToK, ToV>> for SmallMap<FromK, FromV>
where
    FromK: CoerceKey<ToK>,
    FromV: Coerce<ToV>,
{
}

impl<K: Debug, V: Debug> Debug for SmallMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> SmallMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(n: usize) -> Self {
        Self {
            state: MapHolder::with_capacity(n),
        }
    }

    /// Create with largest capacity which is represented by `Vec`.
    pub(crate) fn with_capacity_largest_vec() -> Self {
        Self {
            state: MapHolder::with_capacity_largest_vec(),
        }
    }

    pub fn keys(&self) -> impl ExactSizeIterator<Item = &K> + Clone {
        match self.state {
            MapHolder::Empty => MHKeys::Empty,
            MapHolder::Vec(ref v) => MHKeys::Vec(v.keys()),
            MapHolder::Map(ref m) => MHKeys::Map(m.keys()),
        }
    }

    pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + Clone {
        match self.state {
            MapHolder::Empty => MHValues::Empty,
            MapHolder::Vec(ref v) => MHValues::Vec(v.values()),
            MapHolder::Map(ref m) => MHValues::Map(m.values()),
        }
    }

    pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> {
        match self.state {
            MapHolder::Empty => MHValuesMut::Empty,
            MapHolder::Vec(ref mut v) => MHValuesMut::Vec(v.values_mut()),
            MapHolder::Map(ref mut m) => MHValuesMut::Map(m.values_mut()),
        }
    }

    pub fn iter(&self) -> MHIter<'_, K, V> {
        match self.state {
            MapHolder::Empty => MHIter::Empty,
            MapHolder::Vec(ref v) => MHIter::Vec(v.iter()),
            MapHolder::Map(ref m) => MHIter::Map(m.iter()),
        }
    }

    pub fn iter_hashed(&self) -> impl ExactSizeIterator<Item = (BorrowHashed<K>, &V)> {
        match self.state {
            MapHolder::Empty => MHIterHash::Empty,
            MapHolder::Vec(ref v) => MHIterHash::Vec(v.iter_hashed()),
            MapHolder::Map(ref m) => MHIterHash::Map(m.iter()),
        }
    }

    pub fn into_iter_hashed(self) -> impl ExactSizeIterator<Item = (Hashed<K>, V)> {
        match self.state {
            MapHolder::Empty => MHIntoIterHash::Empty,
            MapHolder::Vec(v) => MHIntoIterHash::Vec(v.into_iter_hashed()),
            MapHolder::Map(m) => MHIntoIterHash::Map(m.into_iter()),
        }
    }

    pub fn iter_mut(&mut self) -> MHIterMut<'_, K, V> {
        match self.state {
            MapHolder::Empty => MHIterMut::Empty,
            MapHolder::Vec(ref mut v) => MHIterMut::Vec(v.iter_mut()),
            MapHolder::Map(ref mut m) => MHIterMut::Map(m.iter_mut()),
        }
    }

    pub fn into_iter(self) -> MHIntoIter<K, V> {
        match self.state {
            MapHolder::Empty => MHIntoIter::Empty,
            MapHolder::Vec(v) => MHIntoIter::Vec(v.into_iter()),
            MapHolder::Map(m) => MHIntoIter::Map(m.into_iter()),
        }
    }

    pub fn get_hashed<Q>(&self, key: BorrowHashed<Q>) -> Option<&V>
    where
        Q: Equivalent<K> + ?Sized,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(ref v) => v.get_hashed(key),
            MapHolder::Map(ref m) => m.get(&key),
        }
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
        K: Eq,
    {
        self.get_hashed(BorrowHashed::new(key))
    }

    pub fn get_full<Q>(&self, key: &Q) -> Option<(usize, &K, &V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(ref v) => v.get_full(BorrowHashed::new(key)),
            MapHolder::Map(ref m) => m
                .get_full(&BorrowHashed::new(key))
                .map(|(i, k, v)| (i, k.key(), v)),
        }
    }

    pub fn get_index_of_hashed<Q>(&self, key: BorrowHashed<Q>) -> Option<usize>
    where
        Q: Equivalent<K> + ?Sized,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(ref v) => v.get_index_of_hashed(key),
            MapHolder::Map(ref m) => m.get_index_of(&key),
        }
    }

    pub fn get_index(&self, index: usize) -> Option<(&K, &V)> {
        match &self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(x) => x.get_index(index),
            MapHolder::Map(m) => m.get_index(index).map(|(k, v)| (k.key(), v)),
        }
    }

    pub fn get_index_of<Q>(&self, key: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<K> + ?Sized,
        K: Eq,
    {
        self.get_index_of_hashed(BorrowHashed::new(key))
    }

    pub fn get_mut_hashed<Q>(&mut self, key: BorrowHashed<Q>) -> Option<&mut V>
    where
        Q: Equivalent<K> + ?Sized,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(ref mut v) => v.get_mut_hashed(key),
            MapHolder::Map(ref mut m) => m.get_mut(&key),
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
        K: Eq,
    {
        self.get_mut_hashed(BorrowHashed::new(key))
    }

    pub fn contains_key_hashed<Q>(&self, key: BorrowHashed<Q>) -> bool
    where
        Q: Equivalent<K> + ?Sized,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => false,
            MapHolder::Vec(ref v) => v.contains_key_hashed(key),
            MapHolder::Map(ref m) => m.contains_key(&key),
        }
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
        K: Eq,
    {
        self.contains_key_hashed(BorrowHashed::new(key))
    }

    pub fn reserve(&mut self, additional: usize)
    where
        K: Eq,
    {
        if additional == 0 {
            return;
        }
        match &mut self.state {
            MapHolder::Empty => {
                self.state = MapHolder::with_capacity(additional);
            }
            MapHolder::Vec(x) => {
                if !x.try_reserve(additional) {
                    let want = additional + x.len();
                    self.upgrade_vec_to_map(want);
                }
            }
            MapHolder::Map(mp) => mp.reserve(additional),
        }
    }

    pub fn capacity(&self) -> usize {
        match &self.state {
            MapHolder::Empty => 0,
            MapHolder::Vec(x) => x.capacity(),
            MapHolder::Map(x) => x.capacity(),
        }
    }

    /// Give a best guess as to how much heap memory is being used.
    /// Used internally, but not exported as this isn't a usual API.
    pub(crate) fn extra_memory(&self) -> usize {
        match &self.state {
            MapHolder::Empty => 0,
            MapHolder::Vec(x) => x.capacity() * mem::size_of::<(K, V)>(),
            MapHolder::Map(x) => {
                // For each entry, IndexMap stores the (K,V), a usize in the hash table, and about 1 byte overhead.
                // Not canonical details, just based on the current implementation.
                let factor = mem::size_of::<(K, V)>() + mem::size_of::<usize>() + 1;
                factor * x.capacity()
            }
        }
    }

    fn upgrade_empty_to_vec(&mut self) -> &mut VecMap<K, V> {
        self.state = MapHolder::Vec(VecMap::default());
        if let MapHolder::Vec(ref mut v) = self.state {
            return v;
        }
        unreachable!()
    }

    fn upgrade_vec_to_map(&mut self, capacity: usize) -> &mut IndexMap<Hashed<K>, V, BuildIdHasher>
    where
        K: Eq,
    {
        let mut holder = MapHolder::Map(IndexMap::with_capacity_and_hasher(
            capacity,
            Default::default(),
        ));
        mem::swap(&mut self.state, &mut holder);

        if let MapHolder::Vec(ref mut v) = holder {
            if let MapHolder::Map(ref mut m) = self.state {
                v.drain_to(m);
                return m;
            }
        }
        unreachable!()
    }

    pub fn insert_hashed(&mut self, key: Hashed<K>, val: V) -> Option<V>
    where
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => self
                .upgrade_empty_to_vec()
                .try_insert_hashed(key, val)
                .unwrap(),
            MapHolder::Map(ref mut m) => m.insert(key, val),
            MapHolder::Vec(ref mut v) => match v.try_insert_hashed(key, val) {
                Ok(v) => v,
                Err(vec_map::InsertCapacityOverflow { key, value }) => {
                    let want = self.len() + 1;
                    self.upgrade_vec_to_map(want).insert(key, value)
                }
            },
        }
    }

    pub fn insert(&mut self, key: K, val: V) -> Option<V>
    where
        K: Hash + Eq,
    {
        self.insert_hashed(Hashed::new(key), val)
    }

    pub fn remove_hashed<Q>(&mut self, key: BorrowHashed<Q>) -> Option<V>
    where
        Q: ?Sized + Equivalent<K>,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(ref mut v) => v.remove_hashed(key),
            MapHolder::Map(ref mut m) => m.shift_remove(&key),
        }
    }

    pub fn remove_hashed_entry<Q>(&mut self, key: BorrowHashed<Q>) -> Option<(K, V)>
    where
        Q: ?Sized + Equivalent<K>,
        K: Eq,
    {
        match self.state {
            MapHolder::Empty => None,
            MapHolder::Vec(ref mut v) => v.remove_hashed_entry(key),
            MapHolder::Map(ref mut m) => m.shift_remove_entry(&key).map(|(k, v)| (k.into_key(), v)),
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Q: ?Sized + Hash + Equivalent<K>,
        K: Eq,
    {
        self.remove_hashed(BorrowHashed::new(key))
    }

    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Q: ?Sized + Hash + Equivalent<K>,
        K: Eq,
    {
        self.remove_hashed_entry(BorrowHashed::new(key))
    }

    pub fn entry_hashed(&mut self, key: Hashed<K>) -> Entry<'_, K, V>
    where
        K: Eq,
    {
        let s = self as *mut Self;

        match self.state {
            MapHolder::Empty => Entry::Vacant(VacantEntry(VacantEntryImpl::Empty(key, self))),
            MapHolder::Vec(ref mut v) => match v.entry_hashed(key) {
                vec_map::Entry::Occupied(e) => {
                    Entry::Occupied(OccupiedEntry(OccupiedEntryImpl::Vec(e)))
                }
                vec_map::Entry::Vacant(e) => Entry::Vacant(VacantEntry(VacantEntryImpl::Vec(e))),
                vec_map::Entry::VacantFull(e) => {
                    // NOTE(nga): `unsafe` here is a work around current limitations
                    //   of borrow checker. It cannot be explained in one sentence,
                    //   if you are interested in details, watch this talk
                    //   https://youtu.be/_agDeiWek8w?t=1485 starting from 24:45.
                    //   This talk describes Polonius, next version of Rust borrow checker
                    //   which should typecheck this code fine.
                    //
                    //   This code is safe because when we `&mut` the raw map pointer,
                    //   we don't hold any borrowed references to the map.
                    Entry::Vacant(VacantEntry(VacantEntryImpl::VecFull(
                        e.into_hashed_key(),
                        unsafe { &mut *s },
                    )))
                }
            },
            MapHolder::Map(ref mut m) => match m.entry(key) {
                indexmap::map::Entry::Occupied(e) => {
                    Entry::Occupied(OccupiedEntry(OccupiedEntryImpl::Map(e)))
                }
                indexmap::map::Entry::Vacant(e) => {
                    Entry::Vacant(VacantEntry(VacantEntryImpl::Map(e)))
                }
            },
        }
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    where
        K: Eq + Hash,
    {
        self.entry_hashed(Hashed::new(key))
    }

    pub fn is_empty(&self) -> bool {
        match self.state {
            MapHolder::Empty => true,
            MapHolder::Vec(ref v) => v.is_empty(),
            MapHolder::Map(ref m) => m.is_empty(),
        }
    }

    pub fn len(&self) -> usize {
        match self.state {
            MapHolder::Empty => 0,
            MapHolder::Vec(ref v) => v.len(),
            MapHolder::Map(ref m) => m.len(),
        }
    }

    pub fn clear(&mut self) {
        self.state = MapHolder::default();
    }
}

enum OccupiedEntryImpl<'a, K, V> {
    Vec(vec_map::OccupiedEntry<'a, K, V>),
    Map(indexmap::map::OccupiedEntry<'a, Hashed<K>, V>),
}

pub struct OccupiedEntry<'a, K, V>(OccupiedEntryImpl<'a, K, V>);

enum VacantEntryImpl<'a, K, V> {
    Empty(Hashed<K>, &'a mut SmallMap<K, V>),
    Vec(vec_map::VacantEntry<'a, K, V>),
    VecFull(Hashed<K>, &'a mut SmallMap<K, V>),
    Map(indexmap::map::VacantEntry<'a, Hashed<K>, V>),
}

pub struct VacantEntry<'a, K, V>(VacantEntryImpl<'a, K, V>);

pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        match self.0 {
            OccupiedEntryImpl::Vec(ref e) => e.key(),
            OccupiedEntryImpl::Map(ref e) => e.key().key(),
        }
    }

    pub fn get(&self) -> &V {
        match self.0 {
            OccupiedEntryImpl::Vec(ref e) => e.get(),
            OccupiedEntryImpl::Map(ref e) => e.get(),
        }
    }

    pub fn get_mut(&mut self) -> &mut V {
        match self.0 {
            OccupiedEntryImpl::Vec(ref mut e) => e.get_mut(),
            OccupiedEntryImpl::Map(ref mut e) => e.get_mut(),
        }
    }
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Eq,
{
    pub fn key(&self) -> &K {
        match self.0 {
            VacantEntryImpl::Empty(ref k, ..) => k.key(),
            VacantEntryImpl::Vec(ref e) => e.key(),
            VacantEntryImpl::VecFull(ref k, ..) => k.key(),
            VacantEntryImpl::Map(ref e) => e.key().key(),
        }
    }

    // NOTE(nga): `VacantEntry::insert` is supposed to return `&'a mut V`
    pub fn insert(self, value: V) {
        match self.0 {
            VacantEntryImpl::Empty(k, map) => {
                map.upgrade_empty_to_vec()
                    .try_insert_hashed(k, value)
                    .unwrap();
            }
            VacantEntryImpl::Vec(e) => {
                e.insert(value);
            }
            VacantEntryImpl::VecFull(k, map) => {
                map.upgrade_vec_to_map(map.len() + 1).insert(k, value);
            }
            VacantEntryImpl::Map(e) => {
                e.insert(value);
            }
        }
    }
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: Eq,
{
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => e.key(),
        }
    }
}

impl<K, V> FromIterator<(K, V)> for SmallMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut mp = Self::with_capacity(iter.size_hint().0);
        for (k, v) in iter {
            mp.insert(k, v);
        }
        mp
    }
}

impl<K, V> FromIterator<(Hashed<K>, V)> for SmallMap<K, V>
where
    K: Eq,
{
    fn from_iter<I: IntoIterator<Item = (Hashed<K>, V)>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut mp = Self::with_capacity(iter.size_hint().0);
        for (k, v) in iter {
            mp.insert_hashed(k, v);
        }
        mp
    }
}

impl<K, V> IntoIterator for SmallMap<K, V> {
    type Item = (K, V);
    type IntoIter = MHIntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a SmallMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = MHIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut SmallMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = MHIterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K: Eq, V: PartialEq> PartialEq for SmallMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.state, &other.state) {
            (MapHolder::Empty, MapHolder::Empty) => true,
            _ => {
                self.len() == other.len()
                    && self
                        .iter_hashed()
                        .all(|(k, v)| other.get_hashed(k) == Some(v))
            }
        }
    }
}

impl<K: Eq, V: Eq> Eq for SmallMap<K, V> {}

impl<K: Hash, V: Hash> Hash for SmallMap<K, V> {
    /// The hash of a map is the sum of hashes of all its elements, so that we guarantee equal hash
    /// means equals
    fn hash<H: Hasher>(&self, state: &mut H) {
        // we could use 'iter_hashed' here, but then we'd be hashing hashes of keys instead of the
        // keys itself, which is a little less correct and flexible.
        self.iter()
            .map(|e| {
                let mut s = DefaultHasher::new();
                e.hash(&mut s);
                std::num::Wrapping(s.finish())
            })
            .sum::<std::num::Wrapping<u64>>()
            .hash(state)
    }
}

impl<K: PartialOrd + Eq, V: PartialOrd> PartialOrd for SmallMap<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K: Ord, V: Ord> Ord for SmallMap<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

/// Create a [`SmallMap`](SmallMap) from a list of key-value pairs.
///
/// ## Example
///
/// ```
/// #[macro_use] extern crate starlark;
/// # fn main() {
///
/// let map = smallmap!{
///     "a" => 1,
///     "b" => 2,
/// };
/// assert_eq!(map.get("a"), Some(&1));
/// assert_eq!(map.get("b"), Some(&2));
/// assert_eq!(map.get("c"), None);
/// # }
/// ```
#[macro_export]
macro_rules! smallmap {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(smallmap!(@single $rest)),*]));

    ($($key:expr => $value:expr,)+) => { smallmap!($($key => $value),+) };
    ($($key:expr => $value:expr),*) => {
        {
            let cap = smallmap!(@count $($key),*);
            let mut map = $crate::collections::SmallMap::with_capacity(cap);
            $(
                map.insert($key, $value);
            )*
            map
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_map() {
        let m = SmallMap::<i8, &str>::new();
        assert_eq!(m.is_empty(), true);
        assert_eq!(m.len(), 0);
        assert_eq!(m.iter().next(), None);
    }

    #[test]
    fn few_entries() {
        let entries1 = vec![(0, 'a'), (1, 'b')];
        let m1 = entries1.iter().cloned().collect::<SmallMap<_, _>>();

        let entries2 = vec![(1, 'b'), (0, 'a')];
        let m2 = entries2.iter().cloned().collect::<SmallMap<_, _>>();
        assert_eq!(m1.is_empty(), false);
        assert_eq!(m1.len(), 2);
        assert_eq!(m2.is_empty(), false);
        assert_eq!(m2.len(), 2);

        assert_eq!(m1.iter().eq(entries1.iter().map(|(k, v)| (k, v))), true);
        assert_eq!(m2.iter().eq(entries2.iter().map(|(k, v)| (k, v))), true);
        assert_eq!(m1.iter().eq(m2.iter()), false);
        assert_eq!(m1.eq(&m1), true);
        assert_eq!(m2.eq(&m2), true);
        assert_eq!(m1, m2);

        assert_eq!(m1.get(&0), Some(&'a'));
        assert_eq!(m1.get(&3), None);
        assert_eq!(m2.get(&1), Some(&'b'));
        assert_eq!(m2.get(&3), None);

        assert_eq!(m1.get_index(0), Some((&0, &'a')));
        assert_eq!(m1.get_index(1), Some((&1, &'b')));
        assert_eq!(m1.get_index(2), None);

        assert_ne!(m1, smallmap! { 0 => 'a', 1 => 'c' });

        let iter = m1.iter();
        let (values1, values2): (Vec<_>, Vec<_>) = (iter.clone().collect(), iter.collect());
        assert_eq!(values1, values2);
    }

    #[test]
    fn many_entries() {
        let numbers = 0..26;
        let letters = 'a'..='z';

        let entries1 = numbers.zip(letters);
        let m1 = entries1.clone().collect::<SmallMap<_, _>>();

        let numbers = (0..26).rev();
        let letters = ('a'..='z').rev();
        let entries2 = numbers.zip(letters);
        let m2 = entries2.clone().collect::<SmallMap<_, _>>();
        assert_eq!(m1.is_empty(), false);
        assert_eq!(m1.len(), 26);
        assert_eq!(m2.is_empty(), false);
        assert_eq!(m2.len(), 26);

        assert_eq!(m1.clone().into_iter().eq(entries1), true);
        assert_eq!(m2.clone().into_iter().eq(entries2), true);
        assert_eq!(m1.iter().eq(m2.iter()), false);
        assert_eq!(m1.eq(&m1), true);
        assert_eq!(m2.eq(&m2), true);
        assert_eq!(m1, m2);

        assert_eq!(m1.get(&1), Some(&'b'));
        assert_eq!(m1.get(&30), None);
        assert_eq!(m2.get(&0), Some(&'a'));
        assert_eq!(m2.get(&30), None);
        assert_eq!(m2.get_full(&0), Some((25, &0, &'a')));
        assert_eq!(m2.get_full(&25), Some((0, &25, &'z')));
        assert_eq!(m2.get_full(&29), None);

        let not_m1 = {
            let mut m = m1.clone();
            m.remove(&1);
            m
        };
        assert_ne!(m1, not_m1);

        let iter = m1.iter();
        let (values1, values2): (Vec<_>, Vec<_>) = (iter.clone().collect(), iter.collect());
        assert_eq!(values1, values2);
    }

    #[test]
    fn test_smallmap_macro() {
        let map = smallmap![1 => "a", 3 => "b"];
        let mut i = map.into_iter();
        assert_eq!(i.next(), Some((1, "a")));
        assert_eq!(i.next(), Some((3, "b")));
        assert_eq!(i.next(), None);
    }

    #[test]
    fn test_clone() {
        let map = smallmap![1 => "a", 3 => "b"];
        let iter = map.iter();
        let values1: Vec<_> = iter.clone().collect();
        let values2: Vec<_> = iter.collect();
        assert_eq!(vec![(&1, &"a"), (&3, &"b")], values1);
        assert_eq!(values1, values2);

        let iter = map.keys();
        let values1: Vec<_> = iter.clone().collect();
        let values2: Vec<_> = iter.collect();
        assert_eq!(vec![&1, &3], values1);
        assert_eq!(values1, values2);

        let iter = map.values();
        let values1: Vec<_> = iter.clone().collect();
        let values2: Vec<_> = iter.collect();
        assert_eq!(vec![&"a", &"b"], values1);
        assert_eq!(values1, values2);
    }

    #[test]
    fn test_duplicate_hashes() {
        // A type which always gives hash collisions
        #[derive(PartialEq, Eq, Debug)]
        struct K(i32);
        #[allow(clippy::derive_hash_xor_eq)]
        impl Hash for K {
            fn hash<H: Hasher>(&self, _state: &mut H) {}
        }

        let mut map = smallmap![K(1) => "test", K(3) => "more"];
        assert_eq!(map.get(&K(1)), Some(&"test"));
        assert_eq!(map.get(&K(2)), None);
        assert_eq!(map.get(&K(3)), Some(&"more"));

        assert_eq!(map.insert(K(2), "magic"), None);
        assert_eq!(map.get(&K(2)), Some(&"magic"));

        assert_eq!(map.remove(&K(1)), Some("test"));
        assert_eq!(map.get(&K(1)), None);
        assert_eq!(map.keys().collect::<Vec<_>>(), vec![&K(3), &K(2)]);
    }

    #[test]
    fn test_smallmap_debug() {
        let s = format!("{:?}", smallmap![1 => "test", 2 => "more"]);
        assert_eq!(s, "{1: \"test\", 2: \"more\"}")
    }

    #[test]
    fn entry() {
        let mut map = SmallMap::new();
        for i in 0..100 {
            match map.entry(i) {
                Entry::Vacant(e) => e.insert(i * 2),
                Entry::Occupied(..) => panic!(),
            }
            match map.entry(i) {
                Entry::Occupied(..) => {}
                Entry::Vacant(..) => panic!(),
            }
        }
    }
}
