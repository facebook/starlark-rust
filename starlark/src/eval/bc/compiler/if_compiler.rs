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
    fragment::{
        expr::{ExprCompiled, MaybeNot},
        span::IrSpanned,
    },
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

/// Common code for compiling if statements and if conditions in comprehensions.
pub(crate) fn write_if_then(
    c: &IrSpanned<ExprCompiled>,
    maybe_not: MaybeNot,
    t: &dyn Fn(&mut BcWriter),
    bc: &mut BcWriter,
) {
    if let ExprCompiled::Not(box ref c) = c.node {
        write_if_then(c, maybe_not.negate(), t, bc);
    } else if let (ExprCompiled::And(box (ref a, ref b)), MaybeNot::Id) = (&c.node, maybe_not) {
        // `if a and b`
        //  |||
        // `if a: if b:
        write_if_then(
            a,
            MaybeNot::Id,
            &|bc| {
                write_if_then(b, MaybeNot::Id, t, bc);
            },
            bc,
        );
    } else if let (ExprCompiled::Or(box (ref a, ref b)), MaybeNot::Not) = (&c.node, maybe_not) {
        // `if not (a or b)`
        //  |||
        // `if (not a) and (not b)`
        write_if_then(
            a,
            MaybeNot::Not,
            &|bc| {
                write_if_then(b, MaybeNot::Not, t, bc);
            },
            bc,
        );
    } else {
        // TODO: handle more and and or
        match maybe_not {
            MaybeNot::Id => {
                c.write_bc(bc);
                bc.write_if(c.span, |bc| t(bc))
            }
            MaybeNot::Not => {
                c.write_bc(bc);
                bc.write_if_not(c.span, |bc| t(bc))
            }
        }
    }
}
