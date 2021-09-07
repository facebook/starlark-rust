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

use crate::{
    collections::{BorrowHashed, Hashed},
    values::{
        dict::{Dict, ValueStr},
        list::List,
        tuple::Tuple,
        Heap, Trace, Tracer, Value,
    },
};
use gazebo::{coerce::Coerce, prelude::*};
use std::fmt::{self, Debug};
use thiserror::Error;

#[derive(Debug, Error)]
enum TypingError {
    /// The value does not have the specified type
    #[error("Value `{0}` of type `{1}` does not match the type annotation `{2}` for {3}")]
    TypeAnnotationMismatch(String, String, String, String),
    /// The given type annotation does not represent a type
    #[error("Type `{0}` is not a valid type annotation")]
    InvalidTypeAnnotation(String),
    /// The given type annotation does not exist, but the user might have forgotten quotes around
    /// it
    #[error(r#"Found `{0}` instead of a valid type annotation. Perhaps you meant `"{1}"`?"#)]
    PerhapsYouMeant(String, String),
}

pub(crate) struct TypeCompiled(Box<dyn for<'v> Fn(Value<'v>) -> bool + Send + Sync>);

unsafe impl Coerce<TypeCompiled> for TypeCompiled {}

unsafe impl<'v> Trace<'v> for TypeCompiled {
    fn trace(&mut self, _tracer: &Tracer<'v>) {
        // Nothing stored here
    }
}

impl Debug for TypeCompiled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("TypeCompiled")
    }
}

impl TypeCompiled {
    pub(crate) fn new<'h>(ty: Value<'h>, heap: &'h Heap) -> anyhow::Result<Self> {
        // Types that are "" are start with "_" are wildcard - they match everything
        fn is_wildcard(x: &str) -> bool {
            x == "" || x.starts_with('_')
        }

        // Dictionary with a single element
        fn unpack_singleton_dictionary<'v>(x: &Dict<'v>) -> Option<(Value<'v>, Value<'v>)> {
            if x.content.len() == 1 {
                x.iter().next()
            } else {
                None
            }
        }

        fn f<'h>(
            ty: Value<'h>,
            heap: &'h Heap,
        ) -> anyhow::Result<Box<dyn for<'v> Fn(Value<'v>) -> bool + Send + Sync>> {
            if let Some(s) = ty.unpack_str() {
                if is_wildcard(s) {
                    Ok(box |_| true)
                } else {
                    match s {
                        "string" => Ok(box |v| {
                            v.unpack_str().is_some() || v.get_ref().matches_type("string")
                        }),
                        "int" => {
                            Ok(box |v| v.unpack_int().is_some() || v.get_ref().matches_type("int"))
                        }
                        "bool" => Ok(box |v| {
                            v.unpack_bool().is_some() || v.get_ref().matches_type("bool")
                        }),
                        _ => {
                            let s = s.to_owned();
                            Ok(box move |v| v.get_ref().matches_type(&s))
                        }
                    }
                }
            } else if ty.is_none() {
                Ok(box |v| v.is_none())
            } else if let Some(t) = Tuple::from_value(ty) {
                let ts = t.content.try_map(|t| f(*t, heap))?;
                Ok(box move |v| match Tuple::from_value(v) {
                    Some(v) if v.len() == ts.len() => v.iter().zip(ts.iter()).all(|(v, t)| t(v)),
                    _ => false,
                })
            } else if let Some(t) = List::from_value(ty) {
                match t.len() {
                    0 => Err(TypingError::InvalidTypeAnnotation(ty.to_str()).into()),
                    1 => {
                        // Must be a list with all elements of this type
                        let t = *t.content.first().unwrap();
                        let wildcard = t.unpack_str().map(is_wildcard) == Some(true);
                        if wildcard {
                            // Any type - so avoid the inner iteration
                            Ok(box |v| List::from_value(v).is_some())
                        } else {
                            let t = f(t, heap)?;
                            Ok(box move |v| match List::from_value(v) {
                                None => false,
                                Some(v) => v.iter().all(|v| t(v)),
                            })
                        }
                    }
                    2 => {
                        // A union type, can match either - special case of the arbitrary choice to go slightly faster
                        let t1 = f(t.content[0], heap)?;
                        let t2 = f(t.content[1], heap)?;
                        Ok(box move |v| t1(v) || t2(v))
                    }
                    _ => {
                        // A union type, can match any
                        let ts = t.content.try_map(|t| f(*t, heap))?;
                        Ok(box move |v| ts.iter().any(|t| t(v)))
                    }
                }
            } else if let Some(t) = Dict::from_value(ty) {
                if t.content.is_empty() {
                    Ok(box |v| Dict::from_value(v).is_some())
                } else if let Some((tk, tv)) = unpack_singleton_dictionary(&t) {
                    // Dict of the form {k: v} must all match the k/v types
                    let tk = f(tk, heap)?;
                    let tv = f(tv, heap)?;
                    Ok(box move |v| match Dict::from_value(v) {
                        None => false,
                        Some(v) => v.content.iter().all(|(k, v)| tk(*k) && tv(*v)),
                    })
                } else {
                    // Dict type, allowed to have more keys that aren't used.
                    // All specified must be type String.
                    let ts = t
                        .iter_hashed()
                        .map(|(k, kt)| {
                            let k_str = match k.key().unpack_str() {
                                None => {
                                    return Err(
                                        TypingError::InvalidTypeAnnotation(ty.to_str()).into()
                                    );
                                }
                                Some(s) => Hashed::new_unchecked(k.hash(), s.to_owned()),
                            };
                            let kt = f(kt, heap)?;
                            Ok((k_str, kt))
                        })
                        .collect::<anyhow::Result<Vec<_>>>()?;

                    Ok(box move |v| match Dict::from_value(v) {
                        None => false,
                        Some(v) => {
                            for (k, kt) in &ts {
                                let ks = ValueStr(k.key().as_str());
                                let kv = BorrowHashed::new_unchecked(k.hash(), &ks);
                                match v.content.get_hashed(kv) {
                                    None => return false,
                                    Some(kv) => {
                                        if !kt(*kv) {
                                            return false;
                                        }
                                    }
                                }
                            }
                            true
                        }
                    })
                }
            } else {
                Err(invalid_type_annotation(ty, heap).into())
            }
        }

        Ok(Self(f(ty, heap)?))
    }
}

fn invalid_type_annotation<'h>(ty: Value<'h>, heap: &'h Heap) -> TypingError {
    if let Some(name) = ty.get_attr("type", heap).and_then(|(_, v)| v.unpack_str()) {
        TypingError::PerhapsYouMeant(ty.to_str(), name.into())
    } else {
        TypingError::InvalidTypeAnnotation(ty.to_str())
    }
}

impl<'v> Value<'v> {
    pub(crate) fn is_type(self, ty: Value<'v>, heap: &'v Heap) -> anyhow::Result<bool> {
        Ok(TypeCompiled::new(ty, heap)?.0(self))
    }

    #[cold]
    #[inline(never)]
    fn check_type_error(value: Value, ty: Value, arg_name: Option<&str>) -> anyhow::Result<()> {
        Err(TypingError::TypeAnnotationMismatch(
            value.to_str(),
            value.get_type().to_owned(),
            ty.to_str(),
            match arg_name {
                None => "return type".to_owned(),
                Some(x) => format!("argument `{}`", x),
            },
        )
        .into())
    }

    pub(crate) fn check_type(
        self,
        ty: Value<'v>,
        arg_name: Option<&str>,
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        if self.is_type(ty, heap)? {
            Ok(())
        } else {
            Self::check_type_error(self, ty, arg_name)
        }
    }

    pub(crate) fn check_type_compiled(
        self,
        ty: Value<'v>,
        ty_compiled: &TypeCompiled,
        arg_name: Option<&str>,
    ) -> anyhow::Result<()> {
        if ty_compiled.0(self) {
            Ok(())
        } else {
            Self::check_type_error(self, ty, arg_name)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_types() {
        let a = assert::Assert::new();
        a.is_true(
            r#"
def f(i: int.type) -> bool.type:
    return i == 3
f(8) == False"#,
        );

        // If the types are either malformed or runtime errors, it should fail
        a.fail("def f(i: made_up):\n pass", "Variable");
        a.fail("def f(i: fail('bad')):\n pass", "bad");

        // Type errors should be caught in arguments
        a.fails(
            "def f(i: bool.type):\n pass\nf(1)",
            &["type annotation", "`1`", "`int`", "`bool`", "`i`"],
        );
        // Type errors should be caught when the user forgets quotes around a valid type
        a.fail("def f(v: bool):\n pass\n", r#"Perhaps you meant `"bool"`"#);
        a.fails(
            r#"Foo = record(value=int.type)
def f(v: bool.type) -> Foo:
    return Foo(value=1)"#,
            &[r#"record(value=field("int"))"#, "Foo"],
        );
        a.fails(
            r#"Bar = enum("bar")
def f(v: Bar):
  pass"#,
            &[r#"enum("bar")"#, "Bar"],
        );
        // Type errors should be caught in return positions
        a.fails(
            "def f() -> bool.type:\n return 1\nf()",
            &["type annotation", "`1`", "`bool`", "`int`", "return"],
        );
        // And for functions without return
        a.fails(
            "def f() -> bool.type:\n pass\nf()",
            &["type annotation", "`None`", "`bool`", "return"],
        );
        // And for functions that return None implicitly or explicitly
        a.fails(
            "def f() -> None:\n return True\nf()",
            &["type annotation", "`None`", "`bool`", "return"],
        );
        a.pass("def f() -> None:\n pass\nf()");

        // The following are all valid types
        a.all_true(
            r#"
is_type(1, int.type)
is_type(True, bool.type)
is_type(True, "")
is_type(None, None)
is_type(assert_type, "function")
is_type([], [int.type])
is_type([], [""])
is_type([1, 2, 3], [int.type])
is_type(None, [None, int.type])
is_type('test', [int.type, str.type])
is_type(('test', None), (str.type, None))
is_type({'1': 'test', '2': False, '3': 3}, {'1': str.type, '2': bool.type})
is_type({"test": 1, "more": 2}, {str.type: int.type})
is_type({1: 1, 2: 2}, {int.type: int.type})

not is_type(1, None)
not is_type((1, 1), str.type)
not is_type({'1': 'test', '3': 'test'}, {'2': bool.type, '3': str.type})
not is_type({'1': 'test', '3': 'test'}, {'1': bool.type, '3': str.type})
not is_type('test', [int.type, bool.type])
not is_type([1,2,None], [int.type])
not is_type({"test": 1, 8: 2}, {str.type: int.type})
not is_type({"test": 1, "more": None}, {str.type: int.type})

is_type(1, "")
is_type([1,2,"test"], ["_a"])
"#,
        );

        // Checking types fails for invalid types
        a.fail("is_type(None, is_type)", "not a valid type");
        a.fail("is_type(None, [])", "not a valid type");
        a.fail("is_type({}, {1: 'string', 2: 'bool'})", "not a valid type");
    }
}
