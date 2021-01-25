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

use crate::values::layout::{
    heap::Walker,
    value::{FrozenValue, FrozenValueMem, Value},
};
use either::Either;
use std::{
    cell::{Ref, RefCell},
    mem,
};

// Starts out as FrozenValue, then changes to Value (must be not frozen)
// Once that change has happened we can never borrow mutably, but can
// borrow without a Ref.
// One exception is GC, but that won't happen while we have references
// outstanding.
pub(crate) struct ThawableCell<'v>(RefCell<Value<'v>>);

impl<'v> ThawableCell<'v> {
    pub fn new(x: FrozenValue) -> Self {
        Self(RefCell::new(Value::new_frozen(x)))
    }

    pub fn get_value(&self) -> Value<'v> {
        *self.0.borrow()
    }

    pub fn get_ref(&self) -> Either<Ref<FrozenValueMem>, Value<'v>> {
        let ptr = unsafe { self.0.try_borrow_unguarded().unwrap() };
        if ptr.unpack_frozen().is_some() {
            Either::Left(Ref::map(self.0.borrow(), |x| x.0.unpack_ptr1().unwrap()))
        } else {
            Either::Right(*ptr)
        }
    }

    pub fn walk(&self, walker: &Walker<'v>) {
        let mut ptr = self.0.borrow_mut();
        walker.walk(&mut *ptr)
    }

    pub fn get_thawed(&self) -> Option<Value<'v>> {
        let ptr = unsafe { self.0.try_borrow_unguarded().unwrap() };
        if ptr.unpack_frozen().is_some() {
            None
        } else {
            Some(*ptr)
        }
    }

    pub fn thaw(&self, f: impl FnOnce(FrozenValue) -> Value<'v>) -> Option<Value<'v>> {
        let mut ptr = self.0.try_borrow_mut().ok()?;
        let fv = ptr.unpack_frozen()?;
        let v = f(fv);
        assert!(v.unpack_frozen().is_none()); // otherwise we might unpack more than once
        *ptr = v;
        mem::drop(ptr);
        self.get_thawed() // Will return a Some
    }
}
