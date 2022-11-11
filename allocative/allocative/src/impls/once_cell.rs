/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

#![cfg(feature = "once_cell")]

use once_cell::sync::OnceCell;

use crate::measure::Allocative;
use crate::measure::Visitor;

impl<T: Allocative> Allocative for OnceCell<T> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut Visitor<'b>) {
        let mut visitor = visitor.enter_self_sized::<Self>();
        if let Some(val) = self.get() {
            val.visit(&mut visitor);
        }
        visitor.exit();
    }
}
