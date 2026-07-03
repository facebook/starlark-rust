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

//! Provides debug-related functionality and utilities.
mod adapter;

mod evaluate;
mod inspect;

pub use adapter::*;

// This is public so it can be used by `starlark_bin`, not part of the supported API
#[doc(hidden)]
pub mod dap {
    // Vendored from https://github.com/microsoft/debug-adapter-protocol/blob/main/debugAdapterProtocol.json
    typify::import_types!("./src/debug/dap.json");
}
