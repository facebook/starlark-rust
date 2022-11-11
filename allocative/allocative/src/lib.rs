/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

#![cfg_attr(rust_nightly, feature(const_type_name))]
#![cfg_attr(rust_nightly, feature(never_type))]

mod allocative_trait;
mod flamegraph;
mod impls;
mod key;
mod rc_str;
mod size_of;
mod test_derive;
mod visitor;

pub use allocative_derive::Allocative;

pub use crate::allocative_trait::Allocative;
pub use crate::flamegraph::FlameGraphBuilder;
pub use crate::key::Key;
pub use crate::size_of::size_of_unique_allocated_data;
pub use crate::visitor::Visitor;
