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
// ?00 => ptr1
// ?01 => ptr2
// ?11 => int (61 bit)
// third bit is a tag set by the user (get_user_tag)

// We group our bytes based on the tag info, not traditional alignment.
// This lint is fairly new, so have to also enable unknown-clippy-lints.
#![allow(clippy::unusual_byte_groupings)]

use std::num::NonZeroUsize;

use gazebo::{cast, phantom::PhantomDataInvariant, prelude::*};
use static_assertions::assert_eq_size;
use void::Void;

// A structure that is morally a `PointerUnpack`, but gets encoded in one
// pointer sized lump. The two types P1 and P2 are arbitrary pointers (which we
// instantiate to FrozenValueMem and ValueMem)
#[derive(Clone_, Copy_, Dupe_)]
pub(crate) struct Pointer<'p1, 'p2, P1, P2> {
    pointer: NonZeroUsize,
    // Make sure we are invariant in all the types/lifetimes.
    // See https://stackoverflow.com/questions/62659221/why-does-a-program-compile-despite-an-apparent-lifetime-mismatch
    phantom: PhantomDataInvariant<(&'p1 P1, &'p2 P2)>,
}

assert_eq_size!(Pointer<'static, 'static, String, String>, usize);
assert_eq_size!(Option<Pointer<'static, 'static, String, String>>, usize);

pub(crate) enum PointerUnpack<'p1, 'p2, P1, P2> {
    Ptr1(&'p1 P1),
    Ptr2(&'p2 P2),
    Int(i32),
}

const TAG_USER: usize = 0b100;

const TAG_BITS: usize = 0b11;
const TAG_P1: usize = 0b000;
const TAG_P2: usize = 0b001;
const TAG_INT: usize = 0b11;

unsafe fn tag_pointer<T>(x: &T, tag: usize) -> usize {
    cast::ptr_to_usize(x) | tag
}

unsafe fn untag_pointer<'a, T>(x: usize) -> &'a T {
    cast::usize_to_ptr(x & !(TAG_BITS | TAG_USER))
}

fn tag_int(x: i32) -> usize {
    ((x as isize) << 3) as usize | TAG_INT
}

fn untag_int(x: usize) -> i32 {
    ((x as isize) >> 3) as i32
}

impl<'p1, 'p2, P1, P2> Pointer<'p1, 'p2, P1, P2> {
    fn new(pointer: usize) -> Self {
        let phantom = PhantomDataInvariant::new();
        // Never zero because the only TAG which is zero is P1, and that must be a pointer
        debug_assert!(pointer != 0);
        let pointer = unsafe { NonZeroUsize::new_unchecked(pointer) };
        Self { pointer, phantom }
    }

    pub fn set_user_tag(self) -> Self {
        Self::new(self.pointer.get() | TAG_USER)
    }

    pub fn new_int(x: i32) -> Self {
        Self::new(tag_int(x))
    }

    pub fn new_ptr1_usize(p1: usize) -> Self {
        Self::new(p1 | TAG_P1)
    }

    pub fn new_ptr2_usize(p2: usize) -> Self {
        Self::new(p2 | TAG_P2)
    }

    pub fn new_ptr1(p1: &'p1 P1) -> Self {
        Self::new(unsafe { tag_pointer(p1, TAG_P1) })
    }

    pub fn new_ptr2(p2: &'p2 P2) -> Self {
        Self::new(unsafe { tag_pointer(p2, TAG_P2) })
    }

    pub fn unpack(self) -> PointerUnpack<'p1, 'p2, P1, P2> {
        let p = self.pointer.get();
        match p & TAG_BITS {
            TAG_P1 => PointerUnpack::Ptr1(unsafe { untag_pointer(p) }),
            TAG_P2 => PointerUnpack::Ptr2(unsafe { untag_pointer(p) }),
            TAG_INT => PointerUnpack::Int(untag_int(p)),
            _ => panic!("Corrupted pointer"),
        }
    }

    pub fn get_user_tag(self) -> bool {
        self.pointer.get() & TAG_USER == TAG_USER
    }

    pub fn unpack_int(self) -> Option<i32> {
        let p = self.pointer.get();
        if p & TAG_BITS == TAG_INT {
            Some(untag_int(p))
        } else {
            None
        }
    }

    pub fn unpack_ptr1(self) -> Option<&'p1 P1> {
        let p = self.pointer.get();
        if p & TAG_BITS == TAG_P1 {
            Some(unsafe { untag_pointer(p) })
        } else {
            None
        }
    }

    pub fn unpack_ptr2(self) -> Option<&'p2 P2> {
        let p = self.pointer.get();
        if p & TAG_BITS == TAG_P2 {
            Some(unsafe { untag_pointer(p) })
        } else {
            None
        }
    }

    pub fn coerce_opt<'p2_, P2_>(self) -> Option<Pointer<'p1, 'p2_, P1, P2_>> {
        let p = self.pointer.get();
        if p & TAG_BITS == TAG_P2 {
            None
        } else {
            // Safe because we aren't a P2, and other than P2, we are equal representation
            Some(Pointer {
                pointer: self.pointer,
                phantom: PhantomDataInvariant::new(),
            })
        }
    }

    pub fn ptr_eq(self, other: Pointer<'_, '_, P1, P2>) -> bool {
        self.pointer == other.pointer
    }

    pub fn ptr_value(self) -> usize {
        self.pointer.get()
    }
}

impl<'p1, P1> Pointer<'p1, '_, P1, Void> {
    // If we have a promise the second parameter isn't used, we can coerce the
    // pointer without unpacking it
    pub fn coerce<'p2, P2>(self) -> Pointer<'p1, 'p2, P1, P2> {
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
