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

use crate::errors::eprint_error;
use std::{fs, path::PathBuf};

pub fn assert_diagnostics(es: &[anyhow::Error]) {
    if !es.is_empty() {
        for e in es {
            eprint_error(e);
        }
        panic!("There was {} parse errors", es.len());
    }
}

/// Get the list of files in the testcase directory which are `.star` (interesting files)
pub fn testcase_files() -> Vec<PathBuf> {
    let mut res = Vec::new();
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("testcases/parse");
    let paths = fs::read_dir(&d).unwrap_or_else(|e| {
        panic!(
            "testcase_files, fs::read_dir({}) failed with {}",
            d.display(),
            e
        )
    });
    for p in paths {
        let path = p.unwrap().path();
        if path.extension().unwrap_or_default() == "star" {
            res.push(path)
        }
    }
    res
}
