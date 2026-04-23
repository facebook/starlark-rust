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

//! Utility to heap allocate arrays of values.

use std::fmt;
use std::fmt::Debug;
use std::mem;
use std::ops::Deref;
use std::ptr;

use allocative::Allocative;
use starlark_derive::NoSerialize;
use starlark_derive::starlark_value;

use crate as starlark;
use crate::any::ProvidesStaticType;
use crate::values::FrozenValueTyped;
use crate::values::StarlarkValue;

#[derive(derive_more::Display, ProvidesStaticType, NoSerialize, Allocative)]
#[repr(C)]
#[display("{:?}", self)]
#[allocative(bound = "")]
pub(crate) struct AnyArray<T: Debug + 'static> {
    pub(crate) len: usize,
    #[allocative(skip)] // TODO(nga): do not skip.
    content: [T; 0],
}

impl<T: Debug + 'static> AnyArray<T> {
    /// Create an empty `AnyArray` with no elements. Safe because there is
    /// nothing to initialize or drop.
    pub(crate) const fn empty() -> AnyArray<T> {
        AnyArray {
            len: 0,
            content: [],
        }
    }

    /// This function is unsafe because it does not initialize content array,
    /// but drops in in destructor.
    pub(crate) unsafe fn new(len: usize) -> AnyArray<T> {
        AnyArray { len, content: [] }
    }

    pub(crate) fn as_slice(&self) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.content.as_ptr(), self.len) }
    }

    pub(crate) fn offset_of_content() -> usize {
        memoffset::offset_of!(Self, content)
    }
}

impl<T: Debug + 'static> Deref for AnyArray<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T: Debug + 'static> Debug for AnyArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("AnyArray").field(&self.as_slice()).finish()
    }
}

// Currently we always allocate in `drop` heap, which is a bit inefficient.
// But we don't allocate much.
impl<T: Debug + 'static> Drop for AnyArray<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.content.as_mut_ptr(),
                self.len,
            ));
        }
    }
}

// We rely on allocation of `AnyArray` in correct heap (drop or non-drop).
// This struct has zero length array of `T`, so check it actually declares it has drop.
const _: () = assert!(mem::needs_drop::<AnyArray<String>>());

#[starlark_value(type = "AnyArray")]
impl<'v, T: Debug + 'static> StarlarkValue<'v> for AnyArray<T> {
    type Canonical = Self;
}

/// A typed reference to a `[T]` slice allocated via [`AnyArray<T>`] on a frozen heap.
///
/// Type alias for `FrozenValueTyped<'static, AnyArray<T>>`.
///
/// This is the array equivalent of [`FrozenAnyValue<T>`](crate::values::any::FrozenAnyValue).
/// Access goes through the `FrozenValueTyped` tagged-pointer path, then auto-derefs
/// through `AnyArray<T>` to reach `[T]`.
pub type FrozenAnyArray<T> = FrozenValueTyped<'static, AnyArray<T>>;

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::AtomicU32;
    use std::sync::atomic::Ordering;

    use dupe::Dupe;

    use crate::register_starlark_any;
    use crate::values::FrozenHeap;

    // Type used for drop test - must be at module level for registration.
    #[derive(Debug, Clone, Dupe)]
    struct IncrementOnDrop(Arc<AtomicU32>);

    // Register IncrementOnDrop for use with alloc_any_slice in pagable mode.
    register_starlark_any!(IncrementOnDrop);

    impl Drop for IncrementOnDrop {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn test_drop() {
        let counter1 = Arc::new(AtomicU32::new(0));
        let counter2 = Arc::new(AtomicU32::new(0));

        let heap = FrozenHeap::new();
        let values = heap.alloc_any_array_value(&[
            IncrementOnDrop(counter1.dupe()),
            IncrementOnDrop(counter1.dupe()),
            IncrementOnDrop(counter2.dupe()),
            IncrementOnDrop(counter1.dupe()),
            IncrementOnDrop(counter2.dupe()),
        ]);

        assert_eq!(5, values.len());

        assert!(Arc::ptr_eq(&counter1, &values[0].0));
        assert!(Arc::ptr_eq(&counter1, &values[1].0));
        assert!(Arc::ptr_eq(&counter2, &values[2].0));
        assert!(Arc::ptr_eq(&counter1, &values[3].0));
        assert!(Arc::ptr_eq(&counter2, &values[4].0));

        // First drop happens when we clone values for the allocation.
        assert_eq!(3, counter1.load(Ordering::SeqCst));
        assert_eq!(2, counter2.load(Ordering::SeqCst));

        drop(heap);

        assert_eq!(6, counter1.load(Ordering::SeqCst));
        assert_eq!(4, counter2.load(Ordering::SeqCst));
    }

    // Register i32 for use with alloc_any_slice in pagable mode.
    register_starlark_any!(i32);

    #[test]
    fn test_allocation_size() {
        let heap = FrozenHeap::new();
        heap.alloc_any_array_value(&[1, 2, 3]);
        let quake = heap.alloc_str("quake");
        // Test array allocation did not overwrite the string.
        assert_eq!(quake.as_str(), "quake");
    }
}
