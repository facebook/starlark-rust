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

use std::{
    alloc::{alloc, dealloc, Layout},
    cell::{Cell, RefCell},
    mem::MaybeUninit,
    slice,
};

/// We'd love to use the real `alloca`, but don't want to blow through the stack space,
/// so define our own wrapper.
/// We use a single continuous buffer. When it needs upgrading, we double it and keep the old one around.
pub(crate) struct Alloca {
    // An alternative design would be to bake the <T> into the type, so all allocations are of the same type.
    // Benchmarking that, even if the most optimistic scenario (just reallocating a single element)
    // the performance difference is only 2%, so keep the flexibility of not needing to predeclare the type.
    alloc: Cell<*mut u8>,
    end: Cell<*mut u8>,
    last_size: Cell<usize>,
    buffers: RefCell<Vec<(*mut u8, Layout)>>,
}

impl Drop for Alloca {
    fn drop(&mut self) {
        for (ptr, layout) in self.buffers.borrow_mut().drain(0..) {
            unsafe { dealloc(ptr, layout) }
        }
    }
}

const INITIAL_SIZE: usize = 1000000; // ~ 1Mb

impl Alloca {
    pub fn new() -> Self {
        Self::with_capacity(INITIAL_SIZE)
    }

    pub fn with_capacity(size: usize) -> Self {
        let layout = Layout::from_size_align(size, 1).unwrap();
        let pointer = unsafe { alloc(layout) };
        Self {
            alloc: Cell::new(pointer),
            end: Cell::new(pointer.wrapping_add(size)),
            last_size: Cell::new(size),
            buffers: RefCell::new(vec![(pointer, layout)]),
        }
    }

    #[inline(never)]
    fn allocate_more(&self, want: Layout) {
        let size = self.last_size.get() * 2 + want.align() + want.size();
        let layout = Layout::from_size_align(size, 1).unwrap();
        let pointer = unsafe { alloc(layout) };
        self.buffers.borrow_mut().push((pointer, layout));
        self.alloc.set(pointer);
        self.last_size.set(size);
        self.end.set(pointer.wrapping_add(size));
    }

    /// Note that the `Drop` for the `T` will not be called. That's safe if there is no `Drop`,
    /// or you call it yourself.
    #[inline(always)]
    pub fn alloca_uninit<T, R>(&self, len: usize, f: impl FnOnce(&mut [MaybeUninit<T>]) -> R) -> R {
        let layout = Layout::array::<T>(len).unwrap();
        let mut offset = self.alloc.get().align_offset(layout.align());
        let mut start = self.alloc.get().wrapping_add(offset);
        let mut stop = start.wrapping_add(layout.size());
        if stop >= self.end.get() {
            self.allocate_more(layout);
            offset = self.alloc.get().align_offset(layout.align());
            start = self.alloc.get().wrapping_add(offset);
            stop = start.wrapping_add(layout.size());
        }
        let old = self.alloc.get();
        self.alloc.set(stop);
        let data = start as *mut MaybeUninit<T>;
        let slice = unsafe { slice::from_raw_parts_mut(data, len) };
        let res = f(slice);
        self.alloc.set(old);
        res
    }

    #[allow(dead_code)] // Dead, but morally a sensible API to provide, and useful for testing
    #[inline(always)]
    pub fn alloca_fill<T: Copy, R>(&self, len: usize, fill: T, f: impl FnOnce(&mut [T]) -> R) -> R {
        self.alloca_uninit(len, |data| {
            for x in data.iter_mut() {
                x.write(fill);
            }
            let data = unsafe { MaybeUninit::slice_assume_init_mut(data) };
            f(data)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alloca() {
        // Use a small capacity to encourage overflow behaviour
        let a = Alloca::with_capacity(100);
        a.alloca_fill(3, 8usize, |xs| {
            xs[0] = 5;
            xs[2] = xs[0] + xs[1] + 15;
            a.alloca_fill(200, 18usize, |ys| {
                assert_eq!(xs[2], 8 + 5 + 15);
                assert_eq!(ys[0], 18);
                assert_eq!(ys[200 - 1], 18);
            });
            a.alloca_fill(3, 1u8, |_| {});
            assert_eq!(xs[2], 8 + 5 + 15);
        })
    }
}
