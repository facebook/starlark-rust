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

// Possible optimisations:
// Encoding none, bool etc in the pointer of frozen value

mod arena;
mod avalue;
mod constant;
mod heap;
mod pointer;
mod pointer_i32;
mod value;
mod value_captured;

pub(crate) use constant::StringValueLike;
pub use constant::{FrozenStringValue, StarlarkStrN, StringValue};
pub use heap::{Freezer, FrozenHeap, FrozenHeapRef, Heap, Tracer};
pub(crate) use pointer_i32::PointerI32;
pub use value::{FrozenValue, Value};
pub(crate) use value_captured::*;
