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

//! Define variants of the evaluation function with different support
//! for the `load(...)` statement.

use crate::environment::FrozenModule;
use anyhow::anyhow;
use gazebo::prelude::*;
use std::collections::HashMap;

/// A trait for loading file using the load statement path.
pub trait FileLoader {
    /// Open the file given by the load statement `path`.
    fn load(&self, path: &str) -> anyhow::Result<FrozenModule>;
}

/// File loader which returns error unconditionally.
pub(crate) struct NoLoadFileLoader;

impl FileLoader for NoLoadFileLoader {
    fn load(&self, _path: &str) -> anyhow::Result<FrozenModule> {
        Err(anyhow!("ErrorFileLoader does not support loading"))
    }
}

/// FileLoader that looks up modules by name from a map
pub struct ReturnFileLoader<'a> {
    pub modules: &'a HashMap<&'a str, &'a FrozenModule>,
}

impl<'a> FileLoader for ReturnFileLoader<'a> {
    fn load(&self, path: &str) -> anyhow::Result<FrozenModule> {
        match self.modules.get(path) {
            Some(v) => Ok(v.dupe()),
            None => Err(anyhow!(
                "ReturnFileLoader does not know the module `{}`",
                path
            )),
        }
    }
}
