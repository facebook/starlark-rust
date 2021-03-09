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

use crate::{
    environment::{FrozenModule, Globals, Module},
    eval::eval,
    syntax::Dialect,
    values::Value,
};
use anyhow::anyhow;
use std::collections::HashMap;

/// A trait for loading file using the load statement path.
pub trait FileLoader {
    /// Open the file given by the load statement `path`.
    fn load(&self, path: &str) -> anyhow::Result<&FrozenModule>;
}

/// File loader which returns error unconditionally.
pub struct NoLoadFileLoader;

impl FileLoader for NoLoadFileLoader {
    fn load(&self, _path: &str) -> anyhow::Result<&FrozenModule> {
        Err(anyhow!("ErrorFileLoader does not support loading"))
    }
}

/// Evaluate a string content, mutate the environment accordingly and return the
/// evaluated value.
///
/// # Arguments
///
/// __This version uses the [`NoLoadFileLoader`] implementation for
/// the file loader__
///
/// * map: the codemap object used for diagnostics
/// * path: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate
/// * dialect: Starlark language dialect
/// * env: the environment to mutate during the evaluation
/// * global: the environment used to resolve type values
pub fn eval_no_load<'v>(
    path: &str,
    content: String,
    dialect: &Dialect,
    env: &'v Module,
    globals: &Globals,
) -> anyhow::Result<Value<'v>> {
    eval(path, content, dialect, env, globals, NoLoadFileLoader)
}

/// FileLoader that looks up modules by name from a map
pub struct ReturnFileLoader<'a> {
    pub modules: &'a HashMap<&'a str, &'a FrozenModule>,
}

impl<'a> FileLoader for ReturnFileLoader<'a> {
    fn load(&self, path: &str) -> anyhow::Result<&FrozenModule> {
        match self.modules.get(path) {
            Some(v) => Ok(v),
            None => Err(anyhow!(
                "ReturnFileLoader does not know the module `{}`",
                path
            )),
        }
    }
}

pub fn eval_with_modules<'v>(
    path: &str,
    content: String,
    dialect: &Dialect,
    env: &'v Module,
    globals: &Globals,
    modules: &HashMap<&str, &FrozenModule>,
) -> anyhow::Result<Value<'v>> {
    eval(
        path,
        content,
        dialect,
        env,
        globals,
        ReturnFileLoader { modules },
    )
}
