/*
 * Copyright 2018 The Starlark in Rust Authors.
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

use std::fmt;
use std::fmt::Display;
use std::ops::Deref;

use gazebo::coerce::coerce;

use crate::values::list::value::display_list;
use crate::values::list::List;
use crate::values::type_repr::StarlarkTypeRepr;
use crate::values::Coerce;
use crate::values::UnpackValue;
use crate::values::Value;

/// Reference to list content.
#[repr(transparent)]
#[derive(Coerce)]
pub struct ListRef<'v> {
    pub(crate) content: [Value<'v>],
}

impl<'v> ListRef<'v> {
    pub(crate) fn new<'a>(slice: &'a [Value<'v>]) -> &'a ListRef<'v> {
        coerce(slice)
    }

    /// List elements.
    pub fn content(&self) -> &[Value<'v>] {
        &self.content
    }

    /// Iterate over the elements in the list.
    pub fn iter<'a>(&'a self) -> impl ExactSizeIterator<Item = Value<'v>> + 'a
    where
        'v: 'a,
    {
        self.content.iter().copied()
    }
}

impl<'v> Deref for ListRef<'v> {
    type Target = [Value<'v>];

    fn deref(&self) -> &[Value<'v>] {
        &self.content
    }
}

impl<'v> Display for ListRef<'v> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_list(&self.content, f)
    }
}

impl<'v> StarlarkTypeRepr for &'v ListRef<'v> {
    fn starlark_type_repr() -> String {
        Vec::<Value<'v>>::starlark_type_repr()
    }
}

impl<'v> UnpackValue<'v> for &'v ListRef<'v> {
    fn expected() -> String {
        "list".to_owned()
    }

    fn unpack_value(value: Value<'v>) -> Option<Self> {
        List::from_value(value)
    }
}