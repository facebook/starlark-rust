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

/// Define the [`get_type`](crate::values::StarlarkValue::get_type) and
/// [`get_type_value`](crate::values::StarlarkValue::get_type_value_static) fields of
/// [`StarlarkValue`](crate::values::StarlarkValue).
#[macro_export]
macro_rules! starlark_type {
    ($typ:expr) => {
        fn get_type(&self) -> &'static str {
            $typ
        }
        fn get_type_value_static() -> $crate::values::FrozenStringValue {
            const N: usize = $typ.len();
            static RES: $crate::values::StarlarkStrN<N> = $crate::values::StarlarkStrN::new($typ);
            RES.erase()
        }
    };
}

/// Reduce boilerplate when making types instances of [`ComplexValue`](crate::values::ComplexValue)
/// - see the [`ComplexValue`](crate::values::ComplexValue) docs for an example.
#[macro_export]
macro_rules! starlark_complex_value {
    ($v:vis $x:ident) => {
        $crate::__macro_refs::item! {
            $v type $x<'v> = [< $x Gen >]<$crate::values::Value<'v>>;
            $v type [< Frozen $x >] = [< $x Gen >]<$crate::values::FrozenValue>;
            $crate::__macro_refs::any_lifetime!($x<'v>);
            $crate::__macro_refs::any_lifetime!([< Frozen $x >]);

            impl<'v> $crate::values::AllocValue<'v> for $x<'v> {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_complex(self)
                }
            }

            impl $crate::values::AllocFrozenValue for [< Frozen $x >] {
                fn alloc_frozen_value(self, heap: &$crate::values::FrozenHeap) -> $crate::values::FrozenValue {
                    heap.alloc_simple(self)
                }
            }

            impl $crate::values::SimpleValue for [< Frozen $x >] {}

            impl<'v> $x<'v> {
                pub fn from_value(x: $crate::values::Value<'v>) -> Option<&'v Self> {
                    if x.unpack_frozen().is_some() {
                        x.downcast_ref::< [< Frozen $x >] >().map($crate::__macro_refs::coerce_ref)
                    } else {
                        x.downcast_ref::< $x<'v> >()
                    }
                }
            }

            impl<'v> $crate::values::FromValue<'v> for $x<'v> {
                fn from_value(x: $crate::values::Value<'v>) -> Option<$crate::values::ARef<'v, Self>> {
                    $x::from_value(x).map(|x| $crate::values::ARef::new_ptr(x))
                }
            }
        }
    };
}

/// Reduce boilerplate when making types instances of [`ComplexValue`](crate::values::ComplexValue)
/// - see the [`ComplexValue`](crate::values::ComplexValue) docs for an example.
#[macro_export]
macro_rules! starlark_complex_values {
    ($x:ident) => {
        $crate::__macro_refs::item! {
            $crate::__macro_refs::any_lifetime!($x<'v>);
            $crate::__macro_refs::any_lifetime!([< Frozen $x >]);

            impl<'v> $crate::values::AllocValue<'v> for $x<'v> {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_complex(self)
                }
            }

            impl $crate::values::AllocFrozenValue for [< Frozen $x >] {
                fn alloc_frozen_value(self, heap: &$crate::values::FrozenHeap) -> $crate::values::FrozenValue {
                    heap.alloc_simple(self)
                }
            }

            impl $crate::values::SimpleValue for [< Frozen $x >] {}

            impl<'v> $x<'v> {
                #[allow(dead_code)]
                fn from_value(
                    x: $crate::values::Value<'v>,
                ) -> Option<$crate::__macro_refs::Either<&'v Self, &'v [< Frozen $x >]>> {
                    if x.unpack_frozen().is_some() {
                        x.downcast_ref().map($crate::__macro_refs::Either::Right)
                    } else {
                        x.downcast_ref().map($crate::__macro_refs::Either::Left)
                    }
                }
            }
        }
    };
}

/// Reduce boilerplate when making types instances of [`SimpleValue`](crate::values::SimpleValue)
/// - see the [`SimpleValue`](crate::values::SimpleValue) docs for an example.
#[macro_export]
macro_rules! starlark_simple_value {
    ($x:ident) => {
        $crate::__macro_refs::item! {
            $crate::__macro_refs::any_lifetime!($x);

            impl<'v> $crate::values::AllocValue<'v> for $x {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_simple(self)
                }
            }

            impl $crate::values::AllocFrozenValue for $x {
                fn alloc_frozen_value(self, heap: &$crate::values::FrozenHeap) -> $crate::values::FrozenValue {
                    heap.alloc_simple(self)
                }
            }

            impl $crate::values::SimpleValue for $x {}

            impl $x {
                pub fn from_value<'v>(x: $crate::values::Value<'v>) -> Option<&'v Self> {
                    $crate::values::ValueLike::downcast_ref::< $x >(x)
                }
            }

            impl<'v> $crate::values::FromValue<'v> for $x {
                fn from_value(x: $crate::values::Value<'v>) -> Option<$crate::values::ARef<'v, Self>> {
                    $x::from_value(x).map(|x| $crate::values::ARef::new_ptr(x))
                }
            }
        }
    };
}
