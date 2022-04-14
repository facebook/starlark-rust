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

use std::str::FromStr;

use gazebo::dupe::Dupe;

/// How to profile starlark code.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Dupe)]
pub enum ProfileMode {
    /// The heap profile mode provides information about the time spent in each function and allocations
    /// performed by each function. Enabling this mode the side effect of disabling garbage-collection.
    /// This profiling mode is the recommended one.
    Heap,
    /// Like heap profile, but writes output comparible with
    /// [flamegraph.pl](https://github.com/brendangregg/FlameGraph/blob/master/flamegraph.pl).
    HeapFlame,
    /// The statement profile mode provides information about time spent in each statement.
    Stmt,
    /// The bytecode profile mode provides information about bytecode instructions.
    Bytecode,
    /// The bytecode profile mode provides information about bytecode instruction pairs.
    BytecodePairs,
    /// Provide output compatible with
    /// [flamegraph.pl](https://github.com/brendangregg/FlameGraph/blob/master/flamegraph.pl).
    Flame,
}

impl FromStr for ProfileMode {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "heap" => Ok(Self::Heap),
            "heap-flame" => Ok(Self::HeapFlame),
            "stmt" => Ok(Self::Stmt),
            "bytecode" => Ok(Self::Bytecode),
            "bytecode-pairs" => Ok(Self::BytecodePairs),
            s => Err(anyhow::anyhow!("Invalid ProfileMode: `{}`", s)),
        }
    }
}
