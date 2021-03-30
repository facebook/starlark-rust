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

use crate::values::{dict::Dict, list::List, tuple::Tuple, Value};
use thiserror::Error;

#[derive(Debug, Error)]
enum TypingError {
    /// The value does not have the specified type
    #[error("Value `{0}` of type `{1}` does not match the type annotation `{2}` for {3}")]
    TypeAnnotationMismatch(String, String, String, String),
    /// The given type annotation does not represent a type
    #[error("Type `{0}` is not a valid type annotation")]
    InvalidTypeAnnotation(String),
}

impl<'v> Value<'v> {
    pub(crate) fn is_type(self, ty: Value<'v>) -> anyhow::Result<bool> {
        // Types that are "" are start with "_" are wildcard - they match everything
        fn is_wildcard(x: &str) -> bool {
            x == "" || x.starts_with('_')
        }

        // Dictionary with a single element
        fn unpack_singleton_dictionary<'v>(x: &Dict<'v>) -> Option<(Value<'v>, Value<'v>)> {
            if x.len() == 1 { x.iter().next() } else { None }
        }

        if let Some(s) = ty.unpack_str() {
            if is_wildcard(s) {
                Ok(true)
            } else {
                Ok(self.get_aref().matches_type(s))
            }
        } else if ty.is_none() {
            Ok(self.is_none())
        } else if let Some(t) = Tuple::from_value(ty) {
            match Tuple::from_value(self) {
                Some(v) if v.len() == t.len() => {
                    for (v, t) in v.iter().zip(t.iter()) {
                        if !v.is_type(t)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            }
        } else if let Some(t) = List::from_value(ty) {
            match t.len() {
                0 => Err(TypingError::InvalidTypeAnnotation(ty.to_str()).into()),
                1 => {
                    // Must be a list with all elements of this type
                    match List::from_value(self) {
                        None => Ok(false),
                        Some(vs) => {
                            let t: Value = t.iter().next().unwrap();
                            if t.unpack_str().map(is_wildcard) == Some(true) {
                                // Any type - so avoid the inner iteration
                                return Ok(true);
                            }
                            for v in vs.iter() {
                                if !v.is_type(t)? {
                                    return Ok(false);
                                }
                            }
                            Ok(true)
                        }
                    }
                }
                _ => {
                    // A union type, can match any
                    for t in t.iter() {
                        if self.is_type(t)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
            }
        } else if let Some(t) = Dict::from_value(ty) {
            match Dict::from_value(self) {
                None => Ok(false),
                Some(v) => {
                    if let Some((kt, vt)) = unpack_singleton_dictionary(&t) {
                        // Dict of the form {k: v} must all match the k/v types
                        for (k, kv) in v.content.iter() {
                            if !k.is_type(kt)? || !kv.is_type(vt)? {
                                return Ok(false);
                            }
                        }
                    } else {
                        // Dict type, allowed to have more keys that aren't used
                        for (k, kt) in t.iter_hashed() {
                            match v.content.get_hashed(k.borrow()) {
                                None => return Ok(false),
                                Some(kv) => {
                                    if !kv.is_type(kt)? {
                                        return Ok(false);
                                    }
                                }
                            }
                        }
                    }
                    Ok(true)
                }
            }
        } else {
            Err(TypingError::InvalidTypeAnnotation(ty.to_str()).into())
        }
    }

    pub(crate) fn check_type(self, ty: Value<'v>, arg_name: Option<&str>) -> anyhow::Result<()> {
        if self.is_type(ty)? {
            Ok(())
        } else {
            Err(TypingError::TypeAnnotationMismatch(
                self.to_str(),
                self.get_type().to_owned(),
                ty.to_str(),
                match arg_name {
                    None => "return type".to_owned(),
                    Some(x) => format!("argument `{}`", x),
                },
            )
            .into())
        }
    }
}
