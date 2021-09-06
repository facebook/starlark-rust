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

use crate::values::{string::StarlarkStr, FrozenValue, SimpleValue, ValueLike};
use gazebo::prelude::*;
use std::{
    borrow::Borrow,
    cmp::Ordering,
    hash::{Hash, Hasher},
    ops::Deref,
};

/// A [`FrozenRef`] is essentially a [`FrozenValue`], and has the same memory and access guarantees
/// as it. However, this keeps the type of the type `T` of the actual [`FrozenValue`] as a
/// reference, allowing manipulation of the actual typed data.
#[derive(Clone_, Dupe_, Copy_, Debug)]
pub struct FrozenRef<T: 'static + ?Sized> {
    value: &'static T,
}

impl<T: 'static + ?Sized> FrozenRef<T> {
    /// Converts `self` into a new reference that points at something reachable from the previous.
    pub fn map<F, U: 'static + ?Sized>(self, f: F) -> FrozenRef<U>
    where
        for<'v> F: FnOnce(&'v T) -> &'v U,
    {
        FrozenRef {
            value: f(self.value),
        }
    }
}

impl FrozenValue {
    pub fn downcast_frozen_ref<T: SimpleValue>(self) -> Option<FrozenRef<T>> {
        self.downcast_ref::<T>().map(|value| FrozenRef { value })
    }

    pub fn downcast_frozen_str(self) -> Option<FrozenRef<str>> {
        self.to_value()
            .unpack_str()
            .map(|value| FrozenRef { value })
    }

    /// Note: see docs about ['Value::unpack_box_str'] about instability
    pub fn downcast_frozen_starlark_str(self) -> Option<FrozenRef<StarlarkStr>> {
        self.to_value()
            .unpack_starlark_str()
            .map(|value| FrozenRef { value })
    }
}

impl<T: ?Sized> Deref for FrozenRef<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.value
    }
}

impl<T: ?Sized> AsRef<T> for FrozenRef<T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<T: ?Sized> Borrow<T> for FrozenRef<T> {
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<T: ?Sized> Borrow<T> for FrozenRef<Box<T>> {
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<T: ?Sized> PartialEq for FrozenRef<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        (&*self as &T).eq(&*other as &T)
    }
}

impl<T: ?Sized> Eq for FrozenRef<T> where T: Eq {}

impl<T: ?Sized> PartialOrd for FrozenRef<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (&*self as &T).partial_cmp(&*other as &T)
    }
}

impl<T: ?Sized> Ord for FrozenRef<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (&*self as &T).cmp(&*other as &T)
    }
}

impl<T: ?Sized> Hash for FrozenRef<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self as &T).hash(state);
    }
}
