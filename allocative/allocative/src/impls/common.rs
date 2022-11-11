/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

use std::mem;

use crate::key::Key;
use crate::measure::Allocative;
use crate::measure::Visitor;

/// "Field" describing allocated but unused capacity (e.g. in `Vec`).
pub(crate) const UNUSED_CAPACITY_NAME: Key = Key::new("unused_capacity");

/// Generic pointee field in types like `Box`.
pub(crate) const PTR_NAME: Key = Key::new("ptr");

/// Generic name for useful data (e.g. in `Vec`).
pub(crate) const DATA_NAME: Key = Key::new("data");

pub(crate) fn visit_generic_map<'a, K: Allocative + 'a, V: Allocative + 'a>(
    visitor: &mut Visitor,
    entries: impl IntoIterator<Item = (&'a K, &'a V)>,
) {
    let mut visitor = visitor.enter_unique(Key::new("data"), mem::size_of::<*const ()>());
    for (k, v) in entries {
        visitor.visit_field(Key::new("key"), k);
        visitor.visit_field(Key::new("value"), v);
    }
    visitor.exit();
}

pub(crate) fn visit_generic_set<'a, K: Allocative + 'a>(
    visitor: &mut Visitor,
    entries: impl IntoIterator<Item = &'a K>,
) {
    let mut visitor = visitor.enter_unique(Key::new("data"), mem::size_of::<*const ()>());
    for k in entries {
        visitor.visit_field(Key::new("key"), k);
    }
    visitor.exit();
}
