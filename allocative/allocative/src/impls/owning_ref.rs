/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

#![cfg(feature = "owning_ref")]

use owning_ref::OwningRef;

use crate::key::Key;
use crate::measure::Allocative;
use crate::measure::Visitor;

impl<O: Allocative, X> Allocative for OwningRef<O, X> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut Visitor<'b>) {
        let mut visitor = visitor.enter_self_sized::<Self>();
        visitor.visit_field(Key::new("owner"), self.as_owner());
        visitor.exit();
    }
}
