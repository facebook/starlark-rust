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

#[macro_export]
macro_rules! starlark_type {
    ($typ:expr) => {
        fn get_type(&self) -> &'static str {
            $typ
        }
        fn get_type_value(&self) -> &'static $crate::values::ConstFrozenValue {
            static RES: $crate::values::ConstFrozenValue =
                $crate::values::ConstFrozenValue::new($typ);
            &RES
        }
    };
}

#[macro_export]
macro_rules! starlark_value {
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

            impl<'v> $crate::values::AllocValue<'v> for [< Frozen $x >] {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_simple(self)
                }
            }

            impl $crate::values::SimpleValue for [< Frozen $x >] {}

            impl<'v> $x<'v> {
                pub fn from_value(x: $crate::values::Value<'v>) -> Option<$crate::values::ARef<'v, $x<'v>>> {
                    fn promote<'v>(x: & [< Frozen $x >]) -> & $x<'v> {
                        unsafe {
                            // Safe because we know Value and FrozenValue have the same bit patterns where they overlap
                            &*(x as *const [< Frozen $x >] as *const $x)
                        }
                    }

                    x.downcast_ref::< [< Frozen $x >] >()
                        .map(|o| $crate::values::ARef::map(o, |e| promote(e)))
                        .or_else(|| x.downcast_ref::<$x<'v>>())
                }

                #[allow(dead_code)]
                pub fn from_value_mut(
                    x: $crate::values::Value<'v>,
                    heap: &'v $crate::values::Heap,
                ) -> anyhow::Result<Option<std::cell::RefMut<'v, $x<'v>>>> {
                    x.downcast_mut::<$x<'v>>(heap)
                }
            }

            $v struct [< Ref $x >]<'v>(pub $crate::values::ARef<'v, $x<'v>>);

            impl<'v> $crate::values::UnpackValue<'v> for [< Ref $x>]<'v> {
                fn unpack_value(value: $crate::values::Value<'v>, _heap: &'v $crate::values::Heap) -> Option<Self> {
                    $x::from_value(value)
                        .map([< Ref $x>])
                }
            }

            impl<'v> std::ops::Deref for [< Ref $x>]<'v> {
                type Target = $x<'v>;

                fn deref(&self) -> &Self::Target {
                    &*self.0
                }
            }
        }
    };
}

#[macro_export]
macro_rules! starlark_simple_value {
    ($v:vis $x:ident) => {
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

            impl<'v> $x {
                pub fn from_value(x: $crate::values::Value<'v>) -> Option<$crate::values::ARef<'v, $x>> {
                    x.downcast_ref::< $x >()
                }
            }

            $v struct [< Ref $x >]<'v>(pub $crate::values::ARef<'v, $x>);

            impl<'v> $crate::values::UnpackValue<'v> for [< Ref $x>]<'v> {
                fn unpack_value(value: $crate::values::Value<'v>, _heap: &'v $crate::values::Heap) -> Option<Self> {
                    $x::from_value(value)
                        .map([< Ref $x>])
                }
            }

            impl<'v> std::ops::Deref for [< Ref $x>]<'v> {
                type Target = $x;

                fn deref(&self) -> &Self::Target {
                    &*self.0
                }
            }
        }
    };
}
