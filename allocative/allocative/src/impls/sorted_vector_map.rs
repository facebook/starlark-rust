/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

#![cfg(feature = "sorted_vector_map")]

use sorted_vector_map::SortedVectorMap;
use sorted_vector_map::SortedVectorSet;

use crate::impls::common::visit_generic_map;
use crate::impls::common::visit_generic_set;
use crate::measure::Allocative;
use crate::measure::Visitor;

impl<K: Allocative + Ord, V: Allocative> Allocative for SortedVectorMap<K, V> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut Visitor<'b>) {
        let mut visitor = visitor.enter_self_sized::<Self>();
        visit_generic_map(&mut visitor, self.iter());
        // TODO(nga): spare capacity.
        visitor.exit();
    }
}

impl<V: Allocative + Ord> Allocative for SortedVectorSet<V> {
    fn visit<'a, 'b: 'a>(&self, visitor: &'a mut Visitor<'b>) {
        let mut visitor = visitor.enter_self_sized::<Self>();
        visit_generic_set(&mut visitor, self.iter());
        // TODO(nga): spare capacity.
        visitor.exit();
    }
}
