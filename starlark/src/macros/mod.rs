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
        paste::item! {
            $v type $x<'v> = [< $x Gen >]<$crate::values::Value<'v>>;
            $v type [< Frozen $x >] = [< $x Gen >]<$crate::values::FrozenValue>;
            any_lifetime!($x<'v>);
            any_lifetime!([< Frozen $x >]);

            impl<'v> $crate::values::AllocValue<'v> for $x<'v> {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_mutable(self)
                }
            }

            impl<'v> $crate::values::AllocFrozenValue<'v> for [< Frozen $x >] {
                fn alloc_frozen_value(self, heap: &'v $crate::values::FrozenHeap) -> $crate::values::FrozenValue {
                    heap.alloc_immutable(self)
                }
            }

            impl<'v> $crate::values::AllocValue<'v> for [< Frozen $x >] {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_immutable(self)
                }
            }

            $v trait [< Mutable $x >]<'v> {
                fn [< mutable_ $x:lower >](&mut self) -> &mut $x<'v>;
            }

            impl<'v> [< Mutable $x >]<'v> for $x<'v> {
                fn [< mutable_ $x:lower >](&mut self) -> &mut $x<'v> {
                    self
                }
            }

            impl<'v> [< Mutable $x >]<'v> for [< Frozen $x >] {
                fn [< mutable_ $x:lower >](&mut self) -> &mut $x<'v> {
                    unreachable!("We only call mutable_ on values which are mutable, and Frozen values should never be in the mutable heap")
                }
            }

            impl<'v> $x<'v> {
                pub fn from_value(x: Value<'v>) -> Option<gazebo::cell::ARef<'v, $x<'v>>> {
                    fn promote<'v>(x: & [< Frozen $x >]) -> & $x<'v> {
                        unsafe {
                            // Safe because we know Value and FrozenValue have the same bit patterns where they overlap
                            &*(x as *const [< Frozen $x >] as *const $x)
                        }
                    }

                    x.downcast_ref::< [< Frozen $x >] >()
                        .map(|o| gazebo::cell::ARef::map(o, |e| promote(e)))
                        .or_else(|| x.downcast_ref::<$x<'v>>())
                }

                pub fn from_value_mut(
                    x: Value<'v>,
                    heap: &'v $crate::values::Heap,
                ) -> anyhow::Result<Option<std::cell::RefMut<'v, $x<'v>>>> {
                    x.downcast_mut::<$x<'v>>(heap)
                }
            }

            $v struct [< Ref $x >]<'v>(pub gazebo::cell::ARef<'v, $x<'v>>);

            impl<'v> $crate::stdlib::UnpackValue<'v> for [< Ref $x>]<'v> {
                fn unpack_value(value: Value<'v>, _heap: &'v $crate::values::Heap) -> Option<Self> {
                    $x::from_value(value)
                        .map([< Ref $x>])
                }
            }
        }
    };
}

#[macro_export]
macro_rules! starlark_immutable_value {
    ($v:vis $x:ident) => {
        paste::item! {
            any_lifetime!($x);

            impl<'v> $crate::values::AllocValue<'v> for $x {
                fn alloc_value(self, heap: &'v $crate::values::Heap) -> $crate::values::Value<'v> {
                    heap.alloc_immutable(self)
                }
            }

            impl<'v> $crate::values::AllocFrozenValue<'v> for $x {
                fn alloc_frozen_value(self, heap: &'v $crate::values::FrozenHeap) -> $crate::values::FrozenValue {
                    heap.alloc_immutable(self)
                }
            }

            impl<'v> ImmutableValue<'v> for $x {}

            impl<'v> $x {
                pub fn from_value(x: Value<'v>) -> Option<gazebo::cell::ARef<'v, $x>> {
                    x.downcast_ref::< $x >()
                }
            }

            $v struct [< Ref $x >]<'v>(pub gazebo::cell::ARef<'v, $x>);

            impl<'v> $crate::stdlib::UnpackValue<'v> for [< Ref $x>]<'v> {
                fn unpack_value(value: Value<'v>, _heap: &'v $crate::values::Heap) -> Option<Self> {
                    $x::from_value(value)
                        .map([< Ref $x>])
                }
            }
        }
    };
}
