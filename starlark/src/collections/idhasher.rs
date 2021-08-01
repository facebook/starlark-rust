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
use std::hash::{BuildHasherDefault, Hasher};

/*
 * IdHasher is a simple hasher that computes
 * a minimal mix to get entropy into the upper 7 bits of a u64.
 *
 * This is important when used with HashBrown, HashMap and IndexMap,
 * which uses the upper 7 bits of the hash for a tag, then compares 16 tags in
 * parallel with a SIMD instruction. Without the mix, typical low-valued u32 ids
 * would all have tag 0.
 */

pub(crate) fn mix_u32(n: u32) -> u64 {
    (n as u64).wrapping_mul(0x9e3779b97f4a7c15)
}

pub(crate) type BuildIdHasher = BuildHasherDefault<IdHasher>;

/// A Hasher, faster than `DefaultHasher`, but can only hash
/// one single pre-hashed u32. That matches `SmallHashResult`.
/// Don't use it for anything that isn't `SmallHashResult`.
#[derive(Debug, Default, Clone, Dupe, Copy)]
pub(crate) struct IdHasher(u64);

impl Hasher for IdHasher {
    fn write(&mut self, _: &[u8]) {
        unimplemented!()
    }

    fn write_u32(&mut self, n: u32) {
        debug_assert_eq!(self.0, 0); // Allow one write per Hasher instance.
        self.0 = mix_u32(n);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}
