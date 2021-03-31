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

//! Types representing Starlark modules ([`Module`] and [`FrozenModule`]) and global variables ([`Globals`]).
//!
//! Global functions and values are stored in [`Globals`], which are typically
//! built using [`GlobalsBuilder`].
//! User executions store their values in a [`Module`], which have to be converted to a
//! [`FrozenModule`] using [`freeze`](Module::freeze) before they can be `load()`'d as a dependency.

mod globals;
mod modules;
pub(crate) mod names;
pub(crate) mod slots;

pub use globals::*;
pub use modules::*;

use thiserror::Error;

#[derive(Debug, Error)]
pub(crate) enum EnvironmentError {
    /// Variables was no found.
    #[error("Variable `{0}` not found")]
    VariableNotFound(String),
    #[error("Local variable `{0}` referenced before assignment")]
    LocalVariableReferencedBeforeAssignment(String),
    /// Cannot import private symbol, i.e. underscore prefixed
    #[error("Cannot import private symbol `{0}`")]
    CannotImportPrivateSymbol(String),
    /// Can't set variables unless in the root name
    #[error("Cannot set variable `{0}` at this point, must be in a non-frozen module context")]
    CannotSetVariable(String),
    #[error("No imports are available, you tried `{0}` (no call to `Evaluator.set_loader`)")]
    NoImportsAvailable(String),
}
