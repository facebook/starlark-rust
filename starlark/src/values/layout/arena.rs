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

//! A heap storing AValue traits. The heap is a sequence of the
//! AValue vtable, followed by the payload.
//! Every payload must be at least 1 usize large (even ZST).
//! Some elements are created using reserve, in which case they point
//! to a BlackHole until they are filled in.
//!
//! Some elements can be overwritten (typically during GC) by a usize.
//! In these cases the bottom bit of the usize as used by the heap
//! to tag it as being a usize, and the word after is the size of the
//! item it replaced.

use crate::values::layout::avalue::{AValue, BlackHole};
use bumpalo::Bump;
use either::Either;
use std::{
    alloc::Layout,
    any::TypeId,
    cmp,
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    ptr::{self, from_raw_parts, metadata, DynMetadata},
};

#[derive(Default)]
pub(crate) struct Arena(Bump);

#[doc(hidden)] // Appears in a trait, but don't want it to
#[repr(transparent)]
pub struct AValuePtr(DynMetadata<dyn AValue<'static>>);

/// Reservation is morally a Reservation<T>, but we treat is as an
/// existential.
/// Tied to the lifetime of the heap.
pub(crate) struct Reservation<'v> {
    typ: TypeId,                   // The type of T
    pointer: *mut (AValuePtr, ()), // Secretly (AValuePtr, T)
    phantom: PhantomData<&'v ()>,
}

impl<'v> Reservation<'v> {
    pub(crate) fn fill<'v2: 'v, T: AValue<'v2>>(self, x: T) {
        assert_eq!(self.typ, T::static_type_id());
        unsafe {
            let p = self.pointer as *mut (AValuePtr, T);
            ptr::write(p, (AValuePtr::new(&x), x));
        }
    }

    pub(crate) fn ptr(&self) -> &'v AValuePtr {
        unsafe { &(*self.pointer).0 }
    }
}

impl Arena {
    pub fn allocated_bytes(&self) -> usize {
        self.0.allocated_bytes()
    }

    fn alloc_empty<'v, 'v2: 'v, T: AValue<'v2>>(&'v self) -> *mut (AValuePtr, T) {
        union OrUsize<T> {
            _a: ManuallyDrop<T>,
            // The usize is used for blackholing, so ensure it's
            // always enough space.
            // For ZST this will mean we double the size. But no one stores ZST's
            // in a heap...
            _b: usize,
        }

        let layout = Layout::new::<(AValuePtr, OrUsize<T>)>();
        assert_eq!(
            layout.align(),
            mem::align_of::<AValuePtr>(),
            "Unexpected alignment in Starlark arena"
        );
        let p = self.0.alloc_layout(layout);
        p.as_ptr() as *mut (AValuePtr, T)
    }

    // Reservation should really be an incremental type
    pub fn reserve<'v, 'v2: 'v, T: AValue<'v2>>(&'v self) -> Reservation<'v> {
        let p = self.alloc_empty::<T>();
        // If we don't have a vtable we can't skip over missing elements to drop,
        // so very important to put in a current vtable
        // We always alloc at least one pointer worth of space, so can write in a one-ST blackhole
        let x = BlackHole(mem::size_of::<T>());
        unsafe {
            ptr::write(p as *mut (AValuePtr, BlackHole), (AValuePtr::new(&x), x))
        };

        Reservation {
            typ: T::static_type_id(),
            pointer: p as *mut (AValuePtr, ()),
            phantom: PhantomData,
        }
    }

    #[allow(clippy::mut_from_ref)] // This is fine for arenas
    pub(crate) fn alloc<'v, 'v2: 'v, T: AValue<'v2>>(&'v self, x: T) -> &'v AValuePtr {
        let p = self.alloc_empty::<T>();
        unsafe {
            ptr::write(p, (AValuePtr::new(&x), x));
            &(*p).0
        }
    }

    fn iter_chunk<'a>(chunk: &'a [MaybeUninit<u8>], mut f: impl FnMut(&'a AValuePtr)) {
        // We only allocate trait ptr then a payload immediately after
        // so find the first trait ptr, see how big it is, and keep skipping.
        let mut p = chunk.as_ptr();
        let end = unsafe { chunk.as_ptr().add(chunk.len()) };
        while p < end {
            let val = unsafe { *(p as *const usize) };
            let n = if val & 1 == 1 {
                // Overwritten, so the next word will be the size of the memory
                unsafe { *(p as *const usize).add(1) }
            } else {
                let ptr: &AValuePtr = unsafe { &*(p as *const AValuePtr) };
                f(ptr);
                ptr.unpack().memory_size()
            };
            let n = cmp::max(n, mem::size_of::<usize>());
            unsafe {
                p = p.add(mem::size_of::<AValuePtr>() + n);
                // We know the alignment requirements will never be greater than AValuePtr
                // since we check that in allocate_empty
                p = p.add(p.align_offset(mem::align_of::<AValuePtr>()));
            }
        }
    }

    // Iterate over the values in the heap in the order they
    // were added.
    // Requires relying on internal bumpalo invariants, since
    // there is no spec to the resulting order.
    pub fn for_each_ordered<'a>(&'a mut self, mut f: impl FnMut(&'a AValuePtr)) {
        // It seems that we get the chunks from most newest to oldest.
        // And within each chunk, the values are filled newest to oldest.
        // So need to do two sets of reversing.
        let chunks = self.0.iter_allocated_chunks().collect::<Vec<_>>();
        // Use a single buffer to reduce allocations, but clear it after use
        let mut buffer = Vec::new();
        for chunk in chunks.iter().rev() {
            Self::iter_chunk(chunk, |x| buffer.push(x));
            buffer.iter().rev().for_each(|x| f(*x));
            buffer.clear();
        }
    }

    // Iterate over the values in the heap in any order
    pub fn for_each_unordered<'a>(&'a mut self, mut f: impl FnMut(&'a AValuePtr)) {
        self.0
            .iter_allocated_chunks()
            .for_each(|chunk| Self::iter_chunk(chunk, &mut f))
    }
}

impl AValuePtr {
    pub(crate) fn new<'a, 'b>(x: &'a dyn AValue<'b>) -> Self
    where
        'b: 'a,
    {
        let metadata: DynMetadata<dyn AValue> = metadata(x);
        // The vtable is invariant based on the lifetime, so this is safe
        let metadata: DynMetadata<dyn AValue<'static>> = unsafe { mem::transmute(metadata) };
        // Check that the LSB is not set, as we reuse that for overwrite
        debug_assert!(unsafe { mem::transmute::<_, usize>(metadata) } & 1 == 0);
        AValuePtr(metadata)
    }

    pub fn unpack<'v>(&'v self) -> &'v dyn AValue<'v> {
        unsafe {
            let res = &*(from_raw_parts((self as *const AValuePtr).add(1) as *const (), self.0));
            mem::transmute::<&'v dyn AValue<'static>, &'v dyn AValue<'v>>(res)
        }
    }

    /// Unpack something that might have been overwritten.
    pub fn unpack_overwrite<'v>(&'v self) -> Either<usize, &'v dyn AValue<'v>> {
        let x = unsafe { *(self as *const AValuePtr as *const usize) };
        if x & 1 == 1 {
            Either::Left(x & !1)
        } else {
            Either::Right(self.unpack())
        }
    }

    /// After performing the overwrite any existing pointers to this value
    /// are corrupted.
    pub unsafe fn overwrite<'v, T>(&'v self, x: usize) -> T {
        assert!(x & 1 == 0, "Can't have the lowest bit set");
        assert_eq!(self.0.layout(), Layout::new::<T>());

        let sz = self.unpack().memory_size();
        let p = self as *const AValuePtr as *const (AValuePtr, T);
        let res = ptr::read(p).1;
        let p = self as *const AValuePtr as *mut usize;
        ptr::write(p, x | 1);
        ptr::write(p.add(1), sz);
        res
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        self.for_each_unordered(|x| {
            // Safe to convert to *mut because we are the only owner
            let x = x.unpack() as *const dyn AValue as *mut dyn AValue;
            unsafe {
                ptr::drop_in_place(x)
            };
        });
        self.0.reset()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::values::layout::avalue::simple;

    fn mk_str(x: &str) -> impl AValue<'static> {
        let x: Box<str> = Box::from(x);
        simple(x)
    }

    fn reserve_str<'v>(arena: &'v Arena) -> Reservation<'v> {
        fn f<'v, 'v2: 'v, T: AValue<'v2>>(arena: &'v Arena, _: T) -> Reservation<'v> {
            arena.reserve::<T>()
        }
        f(arena, mk_str(""))
    }

    #[test]
    fn test_trait_arena_iteration() {
        // We want iteration to proceed in the same order as allocation,
        // otherwise profiling won't work
        const LIMIT: usize = 10000;
        let mut arena = Arena::default();
        let mut reserved = Vec::new();
        for i in 0..LIMIT {
            if i % 100 == 0 {
                let r = reserve_str(&arena);
                reserved.push((r, i));
            } else {
                arena.alloc(mk_str(&i.to_string()));
            }
        }
        assert!(!reserved.is_empty());
        for (r, i) in reserved {
            r.fill(mk_str(&i.to_string()));
        }

        // Not a functional part of the test, just makes sure we go through
        // the interesting cases (last time 56 was sufficient, so 10K is plenty of margin of error)
        assert!(
            arena.0.iter_allocated_chunks().count() > 1,
            "Didn't allocate enough to test properly"
        );
        let mut j = 0;
        arena.for_each_ordered(|i| {
            let mut s = String::new();
            i.unpack().collect_repr(&mut s);
            assert_eq!(s, format!("\"{}\"", j));
            j += 1;
        });
        assert_eq!(j, LIMIT);
        j = 0;
        arena.for_each_unordered(|_| j += 1);
        assert_eq!(j, LIMIT);
    }

    #[test]
    // Make sure that even if there are some blackholes when we drop, we can still walk to heap
    fn drop_with_blackhole() {
        let mut arena = Arena::default();
        arena.alloc(mk_str("test"));
        // reserve but do not fill!
        reserve_str(&arena);
        arena.alloc(mk_str("hello"));
        let mut res = Vec::new();
        arena.for_each_ordered(|x| res.push(x));
        assert_eq!(res.len(), 3);
        assert_eq!(res[0].unpack().unpack_str(), Some("test"));
        assert_eq!(res[2].unpack().unpack_str(), Some("hello"));
    }
}
