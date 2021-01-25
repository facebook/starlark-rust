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

use gazebo::{any::AnyLifetime, cast};
use std::fmt::{self, Debug};

// WARNING: This type isn't a real type, a pointer to this is secretly an i32.
// Therefore, don't derive stuff on it, since it will be wrong.
// However, `AnyLifetime` promises not to peek at its value, so that's fine.
#[derive(AnyLifetime)]
#[repr(C)]
pub(crate) struct PointerI32 {
    _private: (),
}

impl Debug for PointerI32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.get().fmt(f)
    }
}

impl PointerI32 {
    const TAG: usize = 0x100000000;

    pub fn new(x: i32) -> &'static Self {
        // UB if the pointer isn't aligned, or it is zero
        // Alignment is 1, so that's not an issue.
        // To deal with 0's we OR in TAG.
        unsafe { cast::usize_to_ptr(x as usize | Self::TAG) }
    }

    pub fn get(&self) -> i32 {
        cast::ptr_to_usize(self) as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_tag() {
        fn check(x: i32) {
            assert_eq!(x, PointerI32::new(x).get())
        }

        for x in -10..10 {
            check(x)
        }
        check(i32::MAX);
        check(i32::MIN);
    }

    #[test]
    fn test_alignment_int_pointer() {
        assert_eq!(1, std::mem::align_of::<PointerI32>());
    }
}
