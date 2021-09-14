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

// We use pointer tagging on the bottom three bits:
// ?00 => frozen pointer
// ?01 => mutable pointer
// ?10 => int (32 bit)
// third bit is a tag set by the user (get_user_tag)

// We group our bytes based on the tag info, not traditional alignment.
// This lint is fairly new, so have to also enable unknown-clippy-lints.
#![allow(clippy::unusual_byte_groupings)]

use either::Either;
use gazebo::{cast, phantom::PhantomDataInvariant, prelude::*};
use static_assertions::assert_eq_size;
use std::{mem, num::NonZeroUsize};

// A structure that is morally a `PointerUnpack`, but gets encoded in one
// pointer sized lump. The two types P1 and P2 are arbitrary pointers (which we
// instantiate to FrozenValueMem and ValueMem)
#[derive(Clone_, Copy_, Dupe_)]
pub(crate) struct Pointer<'p, P> {
    pointer: NonZeroUsize,
    // Make sure we are invariant in all the types/lifetimes.
    // See https://stackoverflow.com/questions/62659221/why-does-a-program-compile-despite-an-apparent-lifetime-mismatch
    phantom: PhantomDataInvariant<&'p P>,
}

assert_eq_size!(Pointer<'static, String>, usize);
assert_eq_size!(Option<Pointer<'static, String>>, usize);

const TAG_BITS: usize = 0b111;

const TAG_INT: usize = 0b10;
// Pointer to an object, which is not frozen.
// Note, an object can be changed from unfrozen to frozen, not vice versa.
const TAG_UNFROZEN: usize = 0b01;

unsafe fn untag_pointer<'a, T>(x: usize) -> &'a T {
    cast::usize_to_ptr(x & !TAG_BITS)
}

#[allow(clippy::unused_unit)]
const _: () = if mem::size_of::<usize>() > mem::size_of::<i32>() {
    ()
} else {
    panic!("starlark-rust requires 64 bit usize")
};

fn tag_int(x: i32) -> usize {
    ((x as u32 as usize) << 3) | TAG_INT
}

fn untag_int(x: usize) -> i32 {
    const INT_DATA_MASK: usize = 0xffffffff << 3;
    debug_assert!(x & !INT_DATA_MASK == TAG_INT);

    ((x as isize) >> 3) as i32
}

impl<'p, P> Pointer<'p, P> {
    fn new(pointer: usize) -> Self {
        let phantom = PhantomDataInvariant::new();
        // Never zero because the only TAG which is zero is P1, and that must be a pointer
        debug_assert!(pointer != 0);
        let pointer = unsafe { NonZeroUsize::new_unchecked(pointer) };
        Self { pointer, phantom }
    }

    pub fn new_int(x: i32) -> Self {
        Self::new(tag_int(x))
    }

    pub fn new_unfrozen_usize(x: usize) -> Self {
        Self::new(x | TAG_UNFROZEN)
    }

    pub fn new_frozen_usize(x: usize) -> Self {
        Self::new(x)
    }

    pub fn new_unfrozen(x: &'p P) -> Self {
        Self::new_unfrozen_usize(cast::ptr_to_usize(x))
    }

    pub fn new_frozen(x: &'p P) -> Self {
        Self::new_frozen_usize(cast::ptr_to_usize(x))
    }

    pub fn is_unfrozen(self) -> bool {
        self.pointer.get() & TAG_UNFROZEN == TAG_UNFROZEN
    }

    pub fn unpack(self) -> Either<&'p P, i32> {
        let p = self.pointer.get();
        if p & TAG_INT == 0 {
            Either::Left(unsafe { untag_pointer(p) })
        } else {
            Either::Right(untag_int(p))
        }
    }

    pub fn unpack_int(self) -> Option<i32> {
        let p = self.pointer.get();
        if p & TAG_INT == 0 {
            None
        } else {
            Some(untag_int(p))
        }
    }

    pub fn unpack_ptr(self) -> Option<&'p P> {
        let p = self.pointer.get();
        if p & TAG_INT == 0 {
            Some(unsafe { untag_pointer(p) })
        } else {
            None
        }
    }

    /// Unpack pointer when it is known to be not an integer.
    pub(crate) unsafe fn unpack_ptr_no_int_unchecked(self) -> &'p P {
        let p = self.pointer.get();
        debug_assert!(p & TAG_INT == 0);
        untag_pointer(p)
    }

    pub fn ptr_eq(self, other: Pointer<'_, P>) -> bool {
        self.pointer == other.pointer
    }

    pub fn ptr_value(self) -> usize {
        self.pointer.get()
    }

    pub unsafe fn cast_lifetime<'p2>(self) -> Pointer<'p2, P> {
        Pointer {
            pointer: self.pointer,
            phantom: PhantomDataInvariant::new(),
        }
    }
}

#[cfg(test)]
#[test]
fn test_int_tag() {
    fn check(x: i32) {
        assert_eq!(x, untag_int(tag_int(x)))
    }

    for x in -10..10 {
        check(x)
    }
    check(i32::MAX);
    check(i32::MIN);
}
