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

use crate::values::{Freezer, SimpleValue};

/// Need to be implemented for non-simple `StarlarkValue`.
///
/// This is called on freeze of the heap. Must produce a replacement object to place
/// in the frozen heap.
///
/// For relatively simple cases it can be implemented with `#[derive(Freeze)]`.
pub trait Freeze {
    type Frozen: SimpleValue;

    /// Freeze a value. The frozen value _must_ be equal to the original,
    /// and produce the same hash.
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen>;
}
