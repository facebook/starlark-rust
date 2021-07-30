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

use crate::values::layout::{arena::AValuePtr, avalue::VALUE_STR_A_VALUE_PTR, value::FrozenValue};
use gazebo::prelude::*;
use std::intrinsics::copy_nonoverlapping;

/// A constant string that can be converted to a [`FrozenValue`].
#[repr(C)] // Must match this layout on the heap
pub struct ConstFrozenStringN<const N: usize> {
    vtable: AValuePtr,
    size: usize,
    payload: [u8; N],
}

impl<const N: usize> ConstFrozenStringN<N> {
    /// Create a new [`ConstFrozenStringN`] given a string of size `N`.
    /// If the string has a different size it will fail.
    pub const fn new(s: &str) -> Self {
        assert!(N == s.len());
        let mut payload = [0u8; N];
        unsafe {
            copy_nonoverlapping(s.as_ptr(), payload.as_mut_ptr(), N)
        };
        Self {
            vtable: VALUE_STR_A_VALUE_PTR,
            size: N,
            payload,
        }
    }

    /// Obtain the [`FrozenValue`] for a [`ConstFrozenStringN`].
    pub fn unpack(&'static self) -> FrozenValue {
        self.erase().unpack()
    }

    /// Erase the type parameter, giving a slightly nicer user experience.
    pub const fn erase(&'static self) -> ConstFrozenString {
        ConstFrozenString(&self.vtable)
    }
}

/// Define a `&'static` [`str`] that can be converted to a [`FrozenValue`].
///
/// Usually used as:
///
/// ```
/// use starlark::const_frozen_string;
/// use starlark::values::{ConstFrozenString, FrozenValue};
///
/// static RES: ConstFrozenString = const_frozen_string!("magic");
/// let fv: FrozenValue = RES.unpack();
/// assert_eq!(Some("magic"), fv.to_value().unpack_str());
/// ```
#[derive(Copy, Clone, Dupe)]
pub struct ConstFrozenString(&'static AValuePtr);

impl ConstFrozenString {
    /// Obtain the [`FrozenValue`] for a [`ConstFrozenString`].
    pub fn unpack(self) -> FrozenValue {
        FrozenValue::new_ptr(self.0)
    }
}

/// Create a [`ConstFrozenString`].
#[macro_export]
macro_rules! const_frozen_string {
    ($s:expr) => {{
        const N: usize = $s.len();
        static X: starlark::values::ConstFrozenStringN<N> =
            starlark::values::ConstFrozenStringN::new($s);
        X.erase()
    }};
}
