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

//! Parameter conversion utilities for `starlark_module` macros.

use crate::{
    collections::SmallMap,
    values::{dict::Dict, tuple::Tuple, Heap, Value},
};
use std::hash::Hash;

/// Types implementing this type may appear in function parameter types
/// in `starlark_module` macro function signatures.
pub trait UnpackValue<'v>: Sized {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self>;
}

impl<'v> UnpackValue<'v> for &'v str {
    fn unpack_value(value: Value<'v>, _heap: &Heap) -> Option<Self> {
        value.unpack_str()
    }
}

impl<'v> UnpackValue<'v> for Value<'v> {
    fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
        Some(value)
    }
}

impl<'v> UnpackValue<'v> for String {
    fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
        value.unpack_str().map(ToOwned::to_owned)
    }
}

impl UnpackValue<'_> for i32 {
    fn unpack_value(value: Value, _heap: &Heap) -> Option<Self> {
        value.unpack_int()
    }
}

impl UnpackValue<'_> for bool {
    fn unpack_value(value: Value, _heap: &Heap) -> Option<Self> {
        value.unpack_bool()
    }
}

impl<'v, K: UnpackValue<'v> + Hash + Eq, V: UnpackValue<'v>> UnpackValue<'v> for SmallMap<K, V> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let dict = Dict::from_value(value)?;
        let mut r = SmallMap::new();
        for (k, v) in dict.get_content().iter() {
            r.insert(K::unpack_value(*k, heap)?, V::unpack_value(*v, heap)?);
        }
        Some(r)
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for Vec<T> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let mut r = Vec::new();
        for item in &value.iterate(heap).ok()? {
            r.push(T::unpack_value(item, heap)?);
        }
        Some(r)
    }
}

impl<'v, T1: UnpackValue<'v>, T2: UnpackValue<'v>> UnpackValue<'v> for (T1, T2) {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        let t = Tuple::from_value(value)?;
        if t.len() != 2 {
            return None;
        }
        Some((
            T1::unpack_value(t.content[0], heap)?,
            T2::unpack_value(t.content[1], heap)?,
        ))
    }
}

// An Option that is encoded in a value using NoneType::None
pub enum NoneOr<T> {
    None,
    Other(T),
}

impl<T> NoneOr<T> {
    pub fn into_option(self) -> Option<T> {
        match self {
            Self::None => None,
            Self::Other(x) => Some(x),
        }
    }
}

impl<'v, T: UnpackValue<'v>> UnpackValue<'v> for NoneOr<T> {
    fn unpack_value(value: Value<'v>, heap: &'v Heap) -> Option<Self> {
        if value.is_none() {
            Some(NoneOr::None)
        } else {
            T::unpack_value(value, heap).map(NoneOr::Other)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        environment::{GlobalsBuilder, Module},
        eval::eval_no_load,
        stdlib::standard_environment,
        syntax::Dialect,
    };

    use crate as starlark;

    #[starlark_module]
    fn global(builder: &mut GlobalsBuilder) {
        fn cc_binary(name: &str, srcs: Vec<&str>) -> String {
            // real implementation may write it to a global variable
            Ok(format!("{:?} {:?}", name, srcs))
        }
    }

    #[test]
    fn test_simple() {
        let globals = standard_environment().with(global).build();
        let mut child = Module::new("my");

        let r = eval_no_load(
            "test_simple.star",
            "cc_binary(name='star', srcs=['a.cc', 'b.cc'])",
            &Dialect::Extended,
            &mut child,
            &globals,
        )
        .unwrap();

        assert_eq!(r#""star" ["a.cc", "b.cc"]"#, r.to_str());
    }
}
