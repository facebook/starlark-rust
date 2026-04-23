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

use std::convert::Infallible;
use std::mem;

use dupe::Clone_;
use dupe::Copy_;
use dupe::Dupe_;

use crate::values::FrozenHeap;
use crate::values::FrozenHeapRef;
use crate::values::Heap;

/// A reference to a value stored in a frozen heap with a borrowed reference to the heap.
#[derive(Copy_, Clone_, Dupe_)]
pub struct OwnedRefFrozenRef<'f, T: ?Sized + 'static> {
    owner: &'f FrozenHeapRef,
    value: &'f T,
}

impl<'f, T: ?Sized> OwnedRefFrozenRef<'f, T> {
    /// Create a new `OwnedRefFrozenRef` pointing at the given value.
    pub unsafe fn new_unchecked(
        value: &'f T,
        owner: &'f FrozenHeapRef,
    ) -> OwnedRefFrozenRef<'f, T> {
        OwnedRefFrozenRef { owner, value }
    }

    /// Owner heap.
    pub fn owner(&self) -> &'f FrozenHeapRef {
        self.owner
    }

    /// Return a reference to the underlying value.
    pub fn as_ref(self) -> &'f T {
        self.value
    }

    /// Add a reference to a new heap, and return the pointer with the lifetime of the new heap.
    pub fn add_heap_ref<'v>(self, heap: &'v FrozenHeap) -> &'v T {
        heap.add_reference(self.owner);
        unsafe { mem::transmute::<&'f T, &'v T>(self.value) }
    }

    /// Like `add_heap_ref`, but for an unfrozen heap.
    pub fn add_unfrozen_heap_ref<'v>(self, heap: Heap<'v>) -> &'v T {
        heap.add_reference(self.owner);
        unsafe { mem::transmute::<&'f T, &'v T>(self.value) }
    }

    /// Fallible map the reference to another one.
    pub fn try_map_result<F, U: ?Sized, E>(self, f: F) -> Result<OwnedRefFrozenRef<'f, U>, E>
    where
        F: FnOnce(&'f T) -> Result<&'f U, E>,
    {
        Ok(OwnedRefFrozenRef {
            owner: self.owner,
            value: f(self.value)?,
        })
    }

    /// Apply a function to the underlying value. Projection operation.
    pub fn map<F, U: ?Sized>(self, f: F) -> OwnedRefFrozenRef<'f, U>
    where
        F: FnOnce(&'f T) -> &'f U,
    {
        match self.try_map_result(|x| Ok::<_, Infallible>(f(x))) {
            Ok(x) => x,
        }
    }

    /// Optionally map the reference to another one.
    pub fn try_map_option<F, U: ?Sized>(self, f: F) -> Option<OwnedRefFrozenRef<'f, U>>
    where
        F: FnOnce(&'f T) -> Option<&'f U>,
    {
        self.try_map_result(|x| f(x).ok_or(())).ok()
    }
}
