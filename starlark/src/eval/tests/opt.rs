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

//! Optimizer tests.

use crate::eval::{bc::opcode::BcOpcode, tests::bc::test_instrs};

#[test]
fn test_type_is_inlined() {
    test_instrs(
        &[BcOpcode::LoadLocal, BcOpcode::TypeIs, BcOpcode::Return],
        r#"
def is_list(x):
    return type(x) == type([])

def test(x):
    return is_list(x)
    "#,
    )
}
