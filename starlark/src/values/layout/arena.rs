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

use bumpalo::Bump;
use std::{marker::PhantomData, mem::MaybeUninit, ptr};

pub(crate) struct Arena<T> {
    bump: Bump,
    phantom: PhantomData<T>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            bump: Bump::new(),
            phantom: Default::default(),
        }
    }

    pub fn allocated_bytes(&self) -> usize {
        self.bump.allocated_bytes()
    }

    #[allow(clippy::mut_from_ref)] // This is fine for arenas
    pub fn alloc(&self, x: T) -> &mut T {
        self.bump.alloc(x)
    }

    fn iter_chunks(&mut self) -> impl Iterator<Item = &[T]> {
        self.bump.iter_allocated_chunks().map(|chunk| {
            // Safe because we only allocate values of type T into the heap, for particular
            // controlled values of T. Importantly, our T has a size which is a multiple
            // of the alignment, and an alignment less than 16.
            let orig: &[MaybeUninit<u8>] = chunk;
            let real: &[T] = unsafe { slice_cast(orig) };
            real
        })
    }

    // Iterate over the chunks in the heap in the order they
    // were added.
    // Requires relying on internal bumpalo invariants, since
    // there is no spec to the resulting order.
    pub fn for_each<'a>(&'a mut self, mut f: impl FnMut(&'a T)) {
        let chunks = self.iter_chunks().collect::<Vec<_>>();
        chunks
            .iter()
            .rev()
            .for_each(|xs| xs.iter().rev().for_each(|x| f(x)))
    }
}

// Copied from https://github.com/FaultyRAM/slice-cast/blob/master/src/lib.rs
// After the author yanked every version in existence :(
// https://github.com/FaultyRAM/slice-cast/issues/1
//
// We added ADDITION to confirm alignment is correct and avoid UB.
unsafe fn slice_cast<T, U>(e: &[T]) -> &[U] {
    use std::{mem, slice};
    if mem::size_of_val(e) == 0 {
        slice::from_raw_parts(e.as_ptr() as *const U, 0)
    } else {
        assert_eq!(mem::size_of_val(e) % mem::size_of::<U>(), 0);
        // ADDITION: Additional test to check for correct alignment
        assert_eq!((e.as_ptr() as usize) % mem::align_of::<U>(), 0);
        slice::from_raw_parts(
            e.as_ptr() as *const U,
            mem::size_of_val(e) / mem::size_of::<U>(),
        )
    }
}

impl<T> Drop for Arena<T> {
    fn drop(&mut self) {
        for chunk in self.iter_chunks() {
            for x in chunk {
                // Safe to convert to *mut because we are the only owner
                let x = x as *const T as *mut T;
                unsafe { ptr::drop_in_place(x) }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_arena_iteration() {
        // We want iteration to proceed in the same order as allocation,
        // otherwise profiling won't work
        const LIMIT: usize = 10000;
        let mut x = Arena::new();
        for i in 0..LIMIT {
            x.alloc(i);
        }
        // Not a functional part of the test, just makes sure we go through
        // the interesting cases (last time 56 was sufficient, so 10K is plenty of margin of error)
        assert!(
            x.bump.iter_allocated_chunks().count() > 1,
            "Didn't allocate enough to test properly"
        );
        let mut j = 0;
        x.for_each(|i| {
            assert_eq!(*i, j);
            j += 1;
        });
        assert_eq!(j, LIMIT);
    }
}
