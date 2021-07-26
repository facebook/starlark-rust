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
//! Some elements are created using reserve, in which case they point
//! to a BlackHole until they are filled in.

use crate::values::layout::avalue::{AValue, BlackHole, BlackHole0};
use bumpalo::Bump;
use std::{
    alloc::Layout,
    any::TypeId,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ptr::{self, from_raw_parts, metadata, DynMetadata},
};

#[derive(Default)]
pub(crate) struct Arena2(Bump);

#[repr(transparent)]
pub(crate) struct AValuePtr(DynMetadata<dyn AValue<'static>>);

/// Reservation is morally a Reservation<T>, but we treat is as an
/// existential.
/// Tied to the lifetime of the heap.
pub(crate) struct Reservation<'v> {
    typ: TypeId,                   // The type of T
    pointer: *mut (AValuePtr, ()), // Secretly (AValuePtr, T)
    phantom: PhantomData<&'v ()>,
}

impl<'v> Reservation<'v> {
    pub(crate) fn fill<'v2, T: AValue<'v2>>(self, x: T)
    where
        'v2: 'v,
    {
        assert_eq!(self.typ, T::static_type_id());
        unsafe {
            let t: &dyn AValue<'v2> = &x;
            let t: &dyn AValue<'static> = mem::transmute(t);
            let metadata: DynMetadata<dyn AValue<'static>> = metadata(t);
            let p = self.pointer as *mut (AValuePtr, T);
            ptr::write(p, (AValuePtr(metadata), x));
        }
    }

    pub(crate) fn ptr(&self) -> &'v AValuePtr {
        unsafe { &(*self.pointer).0 }
    }
}

impl Arena2 {
    pub fn allocated_bytes(&self) -> usize {
        self.0.allocated_bytes()
    }

    fn alloc_empty<'v, 'v2, T>(&'v self) -> *mut (AValuePtr, T)
    where
        'v2: 'v,
        T: AValue<'v2>,
    {
        let layout = Layout::new::<(AValuePtr, T)>();
        assert_eq!(
            layout.align(),
            mem::align_of::<AValuePtr>(),
            "Unexpected alignment in Starlark arena"
        );
        // Make sure there is enough space for the BlackHole to go
        let layout = layout.pad_to_align();
        let p = self.0.alloc_layout(layout);
        p.as_ptr() as *mut (AValuePtr, T)
    }

    // Reservation should really be an incremental type
    pub fn reserve<'v, 'v2, T>(&'v self) -> Reservation<'v>
    where
        'v2: 'v,
        T: AValue<'v2>,
    {
        let p = self.alloc_empty::<T>();
        // If we don't have a vtable we can't skip over missing elements to drop,
        // so very important to put in a current vtable
        let sz = mem::size_of::<T>();
        if sz == 0 {
            // For ZST we have space for a vtable, but nothing more, so use blackhole0
            // which guarantees it is also a ZST
            let x = BlackHole0;
            let t: &dyn AValue<'static> = &x;
            let metadata: DynMetadata<dyn AValue<'static>> = metadata(t);
            unsafe {
                ptr::write(p as *mut AValuePtr, AValuePtr(metadata))
            };
        } else {
            // We must have at least one pointer worth of space, so can write in a one-ST blackhole
            let x = BlackHole(sz);
            let t: &dyn AValue<'static> = &x;
            let metadata: DynMetadata<dyn AValue<'static>> = metadata(t);
            unsafe {
                ptr::write(p as *mut (AValuePtr, BlackHole), (AValuePtr(metadata), x))
            };
        }

        Reservation {
            typ: T::static_type_id(),
            pointer: p as *mut (AValuePtr, ()),
            phantom: PhantomData,
        }
    }

    #[allow(clippy::mut_from_ref)] // This is fine for arenas
    pub(crate) fn alloc<'v, 'v2, T>(&'v self, x: T) -> &'v AValuePtr
    where
        'v2: 'v,
        T: AValue<'v2>,
    {
        let p = self.alloc_empty::<T>();
        unsafe {
            let t: &dyn AValue<'v2> = &x;
            let t: &dyn AValue<'static> = mem::transmute(t);
            let metadata: DynMetadata<dyn AValue<'static>> = metadata(t);
            ptr::write(p, (AValuePtr(metadata), x));
            &(*p).0
        }
    }

    fn iter_chunk<'a>(chunk: &'a [MaybeUninit<u8>], mut f: impl FnMut(&'a AValuePtr)) {
        // We only allocate trait ptr then a payload immediately after
        // so find the first trait ptr, see how big it is, and keep skipping.
        let mut p = chunk.as_ptr();
        let end = unsafe { chunk.as_ptr().add(chunk.len()) };
        while p < end {
            let ptr: &AValuePtr = unsafe { &*(p as *const AValuePtr) };
            f(ptr);
            let n = ptr.unpack().memory_size();
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
    #[allow(dead_code)] // Used in tests, will be used in heap profiling
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
    pub fn unpack<'v>(&'v self) -> &'v dyn AValue<'v> {
        unsafe {
            let res = &*(from_raw_parts((self as *const AValuePtr).add(1) as *const (), self.0));
            mem::transmute::<&'v dyn AValue<'static>, &'v dyn AValue<'v>>(res)
        }
    }
}

impl Drop for Arena2 {
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

    fn reserve_str<'v>(arena: &'v Arena2) -> Reservation<'v> {
        fn f<'v, 'v2, T>(arena: &'v Arena2, _: T) -> Reservation<'v>
        where
            'v2: 'v,
            T: AValue<'v2>,
        {
            arena.reserve::<T>()
        }
        f(arena, mk_str(""))
    }

    #[test]
    fn test_trait_arena_iteration() {
        // We want iteration to proceed in the same order as allocation,
        // otherwise profiling won't work
        const LIMIT: usize = 10000;
        let mut arena = Arena2::default();
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
        let mut arena = Arena2::default();
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
