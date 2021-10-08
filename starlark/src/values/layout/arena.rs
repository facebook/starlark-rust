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

use std::{
    alloc::Layout,
    cmp,
    collections::HashMap,
    intrinsics::copy_nonoverlapping,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ptr::{self, from_raw_parts, metadata, DynMetadata},
};

use bumpalo::Bump;
use either::Either;
use gazebo::prelude::*;

use crate::values::layout::avalue::{AValue, BlackHole};

#[derive(Default)]
pub(crate) struct Arena {
    /// Arena for things which don't need dropping (e.g. strings)
    non_drop: Bump,
    /// Arena for things which might need dropping (e.g. Vec, with memory on heap)
    drop: Bump,
}

pub(crate) enum WhichBump {
    NonDrop,
    Drop,
}

#[derive(Hash, PartialEq, Eq, Clone)]
#[repr(transparent)]
pub(crate) struct AValueHeader(DynMetadata<dyn AValue<'static>>);

// Implements Copy so this is fine
impl Dupe for AValueHeader {}

/// How object is represented in arena.
#[repr(C)]
pub(crate) struct AValueRepr<T> {
    pub(crate) header: AValueHeader,
    pub(crate) payload: T,
}

/// This is object written over [`AValueRepr`] during GC.
#[repr(C)]
pub(crate) struct AValueForward {
    /// Moved object pointer with lowest bit set.
    forward_ptr: usize,
    /// Size of `<T>`. Does not include [`AValueHeader`].
    object_size: usize,
}

/// Reservation is morally a Reservation<T>, but we treat is as an
/// existential.
/// Tied to the lifetime of the heap.
pub(crate) struct Reservation<'v, 'v2, T: AValue<'v2>> {
    pointer: *mut AValueRepr<T>, // Secretly AValueObject<T>
    phantom: PhantomData<(&'v (), &'v2 T)>,
}

impl<'v, 'v2, T: AValue<'v2>> Reservation<'v, 'v2, T> {
    pub(crate) fn do_fill(&mut self, x: T) {
        unsafe {
            ptr::write(
                self.pointer,
                AValueRepr {
                    header: AValueHeader::new(&x),
                    payload: x,
                },
            );
        }
    }

    pub(crate) fn fill(mut self, x: T) {
        self.do_fill(x)
    }

    pub(crate) fn fill_with_extra<E: Copy>(mut self, x: T, extra: &[E]) {
        self.do_fill(x);
        unsafe {
            let p = self.pointer as *mut AValueRepr<T>;
            (*p).write_extra(extra);
        }
    }

    pub(crate) fn ptr(&self) -> &'v AValueHeader {
        unsafe { &(*self.pointer).header }
    }
}

#[derive(Debug)]
/// Information about the data stored on a heap. Accessible through
/// the function `allocated_summary` available on [`Heap`](crate::values::Heap)
/// and [`FrozenHeap`](crate::values::FrozenHeap)
pub struct HeapSummary {
    /// For each type, give the (number of entries, size of all entries).
    /// The size may be approximate as it includes information from
    /// the approximate [`memory_size`](StarlarkValue::memory_size) function.
    pub summary: HashMap<String, (usize, usize)>,
}

impl Arena {
    pub fn allocated_bytes(&self) -> usize {
        self.drop.allocated_bytes() + self.non_drop.allocated_bytes()
    }

    pub fn available_bytes(&self) -> usize {
        self.drop.chunk_capacity() + self.non_drop.chunk_capacity()
    }

    fn alloc_empty<'v, 'v2: 'v, T: AValue<'v2>>(
        bump: &'v Bump,
        extra: usize,
    ) -> *mut AValueRepr<T> {
        assert!(
            mem::align_of::<T>() <= mem::align_of::<AValueHeader>(),
            "Unexpected alignment in Starlark arena. Type {} has alignment {}, expected <= {}",
            std::any::type_name::<T>(),
            mem::align_of::<T>(),
            mem::align_of::<AValueHeader>()
        );
        // We require at least usize space available for overwrite/blackhole
        let size = mem::size_of::<AValueHeader>()
            + cmp::max(mem::size_of::<T>() + extra, mem::size_of::<usize>());
        let layout = Layout::from_size_align(size, mem::align_of::<AValueHeader>()).unwrap();
        let p = bump.alloc_layout(layout);
        p.as_ptr() as *mut AValueRepr<T>
    }

    // Reservation should really be an incremental type
    pub(crate) fn reserve_with_extra<'v, 'v2: 'v, T: AValue<'v2>>(
        &'v self,
        extra: usize,
    ) -> Reservation<'v, 'v2, T> {
        let p = Self::alloc_empty::<T>(&self.drop, extra);
        // If we don't have a vtable we can't skip over missing elements to drop,
        // so very important to put in a current vtable
        // We always alloc at least one pointer worth of space, so can write in a one-ST blackhole
        let x = BlackHole(mem::size_of::<T>() + extra);
        unsafe {
            ptr::write(
                p as *mut AValueRepr<BlackHole>,
                AValueRepr {
                    header: AValueHeader::new(&x),
                    payload: x,
                },
            )
        };

        Reservation {
            pointer: p as *mut AValueRepr<T>,
            phantom: PhantomData,
        }
    }

    /// Allocate a type `T`.
    pub(crate) fn alloc<'v, 'v2: 'v, T: AValue<'v2>>(
        &'v self,
        which_bump: WhichBump,
        x: T,
    ) -> &'v AValueHeader {
        let bump = match which_bump {
            WhichBump::NonDrop => {
                assert!(!mem::needs_drop::<T>());
                &self.non_drop
            }
            WhichBump::Drop => &self.drop,
        };
        let p = Self::alloc_empty::<T>(bump, 0);
        unsafe {
            ptr::write(
                p,
                AValueRepr {
                    header: AValueHeader::new(&x),
                    payload: x,
                },
            );
            &(*p).header
        }
    }

    /// Allocate a type `T` plus `extra` bytes.
    ///
    /// The type `T` will never be dropped, so had better not do any memory allocation.
    pub(crate) fn alloc_extra_non_drop<'v, 'v2: 'v, T: AValue<'v2>>(
        &'v self,
        x: T,
        extra: usize,
    ) -> *mut AValueRepr<T> {
        assert!(!mem::needs_drop::<T>());

        let p = Self::alloc_empty::<T>(&self.non_drop, extra);
        unsafe {
            ptr::write(
                p,
                AValueRepr {
                    header: AValueHeader::new(&x),
                    payload: x,
                },
            );
            p
        }
    }

    fn iter_chunk<'a>(chunk: &'a [MaybeUninit<u8>], mut f: impl FnMut(&'a AValueHeader)) {
        // We only allocate trait ptr then a payload immediately after
        // so find the first trait ptr, see how big it is, and keep skipping.
        let mut p = chunk.as_ptr();
        let end = unsafe { chunk.as_ptr().add(chunk.len()) };
        while p < end {
            let val = unsafe { *(p as *const usize) };
            let n = if val & 1 == 1 {
                // Overwritten, so the next word will be the size of the memory
                unsafe { (*(p as *const AValueForward)).object_size }
            } else {
                let ptr: &AValueHeader = unsafe { &*(p as *const AValueHeader) };
                f(ptr);
                ptr.unpack().memory_size()
            };
            let n = cmp::max(n, mem::size_of::<usize>());
            unsafe {
                p = p.add(mem::size_of::<AValueHeader>() + n);
                // We know the alignment requirements will never be greater than AValuePtr
                // since we check that in allocate_empty
                p = p.add(p.align_offset(mem::align_of::<AValueHeader>()));
            }
        }
    }

    // Iterate over the values in the heap in the order they
    // were added.
    // Requires relying on internal bumpalo invariants, since
    // there is no spec to the resulting order.
    pub fn for_each_ordered<'a>(&'a mut self, mut f: impl FnMut(&'a AValueHeader)) {
        // It seems that we get the chunks from most newest to oldest.
        // And within each chunk, the values are filled newest to oldest.
        // So need to do two sets of reversing.
        for bump in [&mut self.drop, &mut self.non_drop] {
            let chunks = bump.iter_allocated_chunks().collect::<Vec<_>>();
            // Use a single buffer to reduce allocations, but clear it after use
            let mut buffer = Vec::new();
            for chunk in chunks.iter().rev() {
                Self::iter_chunk(chunk, |x| buffer.push(x));
                buffer.iter().rev().for_each(|x| f(*x));
                buffer.clear();
            }
        }
    }

    // Iterate over the values in the drop bump in any order
    pub fn for_each_drop_unordered<'a>(&'a mut self, mut f: impl FnMut(&'a AValueHeader)) {
        self.drop
            .iter_allocated_chunks()
            .for_each(|chunk| Self::iter_chunk(chunk, &mut f))
    }

    // For each Rust-level type (the String) report how many entries there are in the heap, and how much size they consume
    pub fn allocated_summary(&self) -> HeapSummary {
        #[cold] // Try and avoid problematic UB :-(
        #[inline(never)]
        fn for_each<'a>(bump: &'a Bump, mut f: impl FnMut(&'a AValueHeader)) {
            // We have a problem that `iter_allocated_chunks` requires a &mut, and for things like
            // FrozenModule we don't have a mutable Bump. The only reason that the function requires &mut
            // is to make sure new values don't get allocated while you have references to old values,
            // but that's not a problem for us, since we immediately use the values and don't keep them around.
            //
            // We have requested an alternative function in terms of *const, which would be safe,
            // but until that arrives, we cast the & pointer to &mut, accepting a small amount of UB.
            // See https://github.com/fitzgen/bumpalo/issues/121.
            //
            // This might not be safe if the function `f` allocated on the heap,
            // but since this is a local function with a controlled closure, we know that it doesn't.
            #[allow(clippy::cast_ref_to_mut)]
            let bump = unsafe { &mut *(bump as *const Bump as *mut Bump) };
            bump.iter_allocated_chunks()
                .for_each(|chunk| Arena::iter_chunk(chunk, &mut f))
        }

        // Record how many times each header occurs
        // We deliberately hash by the AValueHeader for higher performance, less type lookup
        let mut entries: HashMap<AValueHeader, (&'static str, (usize, usize))> = HashMap::new();
        let mut f = |x: &AValueHeader| {
            let v = x.unpack();
            let e = entries
                .entry(x.dupe())
                .or_insert_with(|| (v.get_type(), (0, 0)));
            e.1.0 += 1;
            e.1.1 += v.total_memory()
        };
        for_each(&self.drop, &mut f);
        for_each(&self.non_drop, &mut f);

        // For a given type, the AValueHeader isn't always unique
        // (if they get compiled in different translation units),
        // so not just a simple map.
        let mut summary = HashMap::new();
        for (_, (name, (count, memory))) in entries {
            let v = summary.entry(name.to_owned()).or_insert((0, 0));
            v.0 += count;
            v.1 += memory;
        }
        HeapSummary { summary }
    }
}

impl AValueHeader {
    pub(crate) fn new<'a, 'b>(x: &'a dyn AValue<'b>) -> Self
    where
        'b: 'a,
    {
        let metadata: DynMetadata<dyn AValue> = metadata(x);
        // The vtable is invariant based on the lifetime, so this is safe
        let metadata: DynMetadata<dyn AValue<'static>> = unsafe { mem::transmute(metadata) };
        // Check that the LSB is not set, as we reuse that for overwrite
        debug_assert!(unsafe { mem::transmute::<_, usize>(metadata) } & 1 == 0);
        AValueHeader(metadata)
    }

    pub(crate) const fn with_metadata(metadata: DynMetadata<dyn AValue<'static>>) -> Self {
        AValueHeader(metadata)
    }

    pub(crate) fn unpack<'v>(&'v self) -> &'v dyn AValue<'v> {
        unsafe {
            let self_repr = self.as_repr::<()>();
            let res = &*(from_raw_parts(&self_repr.payload, self.0));
            mem::transmute::<&'v dyn AValue<'static>, &'v dyn AValue<'v>>(res)
        }
    }

    /// Unpack something that might have been overwritten.
    pub(crate) fn unpack_overwrite<'v>(&'v self) -> Either<usize, &'v dyn AValue<'v>> {
        let x = unsafe { *(self as *const AValueHeader as *const usize) };
        if x & 1 == 1 {
            Either::Left(x & !1)
        } else {
            Either::Right(self.unpack())
        }
    }

    /// After performing the overwrite any existing pointers to this value
    /// are corrupted.
    pub unsafe fn overwrite<'v, T: AValue<'v>>(me: *mut AValueHeader, x: usize) -> T {
        assert!(x & 1 == 0, "Can't have the lowest bit set");
        assert_eq!((*me).0.layout(), Layout::new::<T>());

        let sz = (*me).unpack().memory_size();
        let p = me as *const AValueRepr<T>;
        let res = ptr::read(p).payload;
        let p = me as *mut AValueForward;
        *p = AValueForward {
            forward_ptr: x | 1,
            object_size: sz,
        };
        res
    }

    /// Cast header pointer to repr pointer.
    pub(crate) unsafe fn as_repr<T>(&self) -> &AValueRepr<T> {
        &*(self as *const AValueHeader as *const AValueRepr<T>)
    }
}

impl<T> AValueRepr<T> {
    pub(crate) const fn with_metadata(
        metadata: DynMetadata<dyn AValue<'static>>,
        payload: T,
    ) -> AValueRepr<T> {
        AValueRepr {
            header: AValueHeader::with_metadata(metadata),
            payload,
        }
    }

    pub unsafe fn write_extra<E: Copy>(&self, extra: &[E]) {
        debug_assert_eq!(
            self.header.unpack().memory_size(),
            mem::size_of::<T>() + (extra.len() * mem::size_of::<E>())
        );
        debug_assert!(Layout::new::<T>().padding_needed_for(mem::align_of::<E>()) == 0);
        copy_nonoverlapping(extra.as_ptr(), self.get_extra(), extra.len());
    }

    pub unsafe fn get_extra<E: Copy>(&self) -> *mut E {
        // sanity check
        assert_ne!(mem::size_of::<T>(), 0);

        let p = self as *const AValueRepr<T> as *mut u8;
        let extra = p.add(mem::size_of::<AValueRepr<T>>()) as *mut E;
        debug_assert!(extra as usize % mem::align_of::<E>() == 0);
        extra
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        self.for_each_drop_unordered(|x| {
            // Safe to convert to *mut because we are the only owner
            let x = x.unpack() as *const dyn AValue as *mut dyn AValue;
            unsafe {
                ptr::drop_in_place(x)
            };
        });
        self.non_drop.reset();
        self.drop.reset();
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::values::{any::StarlarkAny, layout::avalue::simple};

    fn to_repr(x: &AValueHeader) -> String {
        let mut s = String::new();
        x.unpack().collect_repr(&mut s);
        s
    }

    fn mk_str(x: &str) -> impl AValue<'static> {
        simple(StarlarkAny::new(x.to_owned()))
    }

    fn reserve_str<'v, T: AValue<'static>>(arena: &'v Arena, _: &T) -> Reservation<'v, 'static, T> {
        arena.reserve_with_extra::<T>(0)
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
                let r = reserve_str(&arena, &mk_str(""));
                reserved.push((r, i));
            } else {
                arena.alloc(WhichBump::Drop, mk_str(&i.to_string()));
            }
        }
        assert!(!reserved.is_empty());
        for (r, i) in reserved {
            r.fill(mk_str(&i.to_string()));
        }

        // Not a functional part of the test, just makes sure we go through
        // the interesting cases (last time 56 was sufficient, so 10K is plenty of margin of error)
        assert!(
            arena.drop.iter_allocated_chunks().count() > 1,
            "Didn't allocate enough to test properly"
        );
        let mut j = 0;
        arena.for_each_ordered(|i| {
            assert_eq!(to_repr(i), j.to_string());
            j += 1;
        });
        assert_eq!(j, LIMIT);
        j = 0;
        arena.for_each_drop_unordered(|_| j += 1);
        assert_eq!(j, LIMIT);
    }

    #[test]
    // Make sure that even if there are some blackholes when we drop, we can still walk to heap
    fn drop_with_blackhole() {
        let mut arena = Arena::default();
        arena.alloc(WhichBump::Drop, mk_str("test"));
        // reserve but do not fill!
        reserve_str(&arena, &mk_str(""));
        arena.alloc(WhichBump::Drop, mk_str("hello"));
        let mut res = Vec::new();
        arena.for_each_ordered(|x| res.push(x));
        assert_eq!(res.len(), 3);
        assert_eq!(to_repr(res[0]), "test");
        assert_eq!(to_repr(res[2]), "hello");
    }

    #[test]
    fn test_allocated_summary() {
        let arena = Arena::default();
        arena.alloc(WhichBump::Drop, mk_str("test"));
        arena.alloc(WhichBump::Drop, mk_str("test"));
        let res = arena.allocated_summary().summary;
        assert_eq!(res.len(), 1);
        let entry = res.values().next().unwrap();
        assert_eq!(entry.0, 2);
        assert_eq!(entry.1, arena.allocated_bytes());
    }
}
