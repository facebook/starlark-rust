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

use crate::eval::{
    bc::writer::BcWriter,
    fragment::{expr::ExprCompiled, span::IrSpanned},
};

/// Common code for compiling if statements and if expressions.
pub(crate) fn write_if_else(
    c: &IrSpanned<ExprCompiled>,
    t: impl FnOnce(&mut BcWriter),
    f: impl FnOnce(&mut BcWriter),
    bc: &mut BcWriter,
) {
    if let ExprCompiled::Not(box ref c) = c.node {
        write_if_else(c, f, t, bc);
    } else {
        // TODO: handle and and or
        c.write_bc(bc);
        bc.write_if_else(c.span, t, f);
    }
}
