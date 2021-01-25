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
use indexmap::Equivalent;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

#[derive(Hash, Eq, PartialEq, Clone, Copy, Dupe, Debug, Default)]
pub struct SmallHashResult(u32);

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub struct Hashed<K> {
    hash: SmallHashResult,
    key: K,
}

#[derive(Copy, Clone)]
pub struct BorrowHashed<'a, Q: ?Sized> {
    hash: SmallHashResult,
    key: &'a Q,
}

impl SmallHashResult {
    pub fn new<K: Hash + ?Sized>(key: &K) -> Self {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        Self::new_unchecked(hasher.finish())
    }

    pub fn new_unchecked(hash: u64) -> Self {
        // NOTE: Here we throw away half the key material we are given,
        // taking only the lower 32 bits.
        // Not a problem because `DefaultHasher` produces well-swizzled bits.
        Self(hash as u32)
    }
}

impl<'a, Q: ?Sized> BorrowHashed<'a, Q> {
    pub fn new(key: &'a Q) -> Self
    where
        Q: Hash,
    {
        Self::new_unchecked(SmallHashResult::new(key), key)
    }

    pub fn new_unchecked(hash: SmallHashResult, key: &'a Q) -> Self {
        Self { hash, key }
    }

    pub fn hash(&self) -> SmallHashResult {
        self.hash
    }

    pub fn key(&self) -> &'a Q {
        self.key
    }
}

impl<'a, Q: Clone> BorrowHashed<'a, Q> {
    pub fn unborrow_clone(&self) -> Hashed<Q> {
        Hashed::new_unchecked(self.hash, self.key.clone())
    }
}

impl<'a, Q: Copy> BorrowHashed<'a, Q> {
    pub fn unborrow_copy(&self) -> Hashed<Q> {
        Hashed::new_unchecked(self.hash, *self.key)
    }
}

impl<'a, Q, K> Equivalent<Hashed<K>> for BorrowHashed<'a, Q>
where
    Q: Equivalent<K> + ?Sized,
{
    fn equivalent(&self, key: &Hashed<K>) -> bool {
        self.hash == key.hash && self.key.equivalent(&key.key)
    }
}

impl<'a, Q: ?Sized> Hash for BorrowHashed<'a, Q> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}

// We deliberately know that this is a hash and value, so our Eq/Hash are fine
#[allow(clippy::derive_hash_xor_eq)]
impl<K> Hash for Hashed<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}

impl<K> Hashed<K> {
    pub fn new(key: K) -> Self
    where
        K: Hash,
    {
        Self::new_unchecked(SmallHashResult::new(&key), key)
    }

    pub fn new_unchecked(hash: SmallHashResult, key: K) -> Self {
        Self { hash, key }
    }

    pub fn key(&self) -> &K {
        &self.key
    }

    pub fn into_key(self) -> K {
        self.key
    }

    pub fn hash(&self) -> SmallHashResult {
        self.hash
    }

    pub fn borrow(&self) -> BorrowHashed<K> {
        BorrowHashed::new_unchecked(self.hash, &self.key)
    }
}

#[cfg(test)]
mod tests {
    use crate::collections::{BorrowHashed, Hashed};
    use indexmap::map::IndexMap;

    #[test]
    fn borrow_and_hashed_equivalent() {
        let mut m = IndexMap::new();
        m.insert(Hashed::new(1), 'b');

        assert_eq!(m.get(&BorrowHashed::new(&1)), Some(&'b'));
    }
}
