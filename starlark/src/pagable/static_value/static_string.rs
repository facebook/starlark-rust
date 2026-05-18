/*
 * Copyright 2026 The Starlark in Rust Authors.
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

//! Static string value registry.
//!
//! This module provides bidirectional mappings between static string value
//! addresses/IDs (empty string and single ASCII characters).

use std::collections::HashMap;
use std::sync::LazyLock;

use super::get_static_value_id::StaticValueId;
use super::get_static_value_id::hash_empty_string;
use super::get_static_value_id::hash_short_string;
use crate::values::FrozenValue;
use crate::values::layout::static_string::VALUE_BYTE_STRINGS;
use crate::values::layout::static_string::VALUE_EMPTY_STRING;

/// Bidirectional lookup maps for static strings.
///
/// The two maps are inverses of each other:
/// - `addr_to_id`: pointer address → `StaticValueId` (for serialization)
/// - `id_to_value`: `StaticValueId` → `FrozenValue` (for deserialization)
pub(super) struct StaticStringMaps {
    pub(super) addr_to_id: HashMap<usize, StaticValueId>,
    pub(super) id_to_value: HashMap<StaticValueId, FrozenValue>,
}

pub(super) static STATIC_STRING_MAPS: LazyLock<StaticStringMaps> = LazyLock::new(|| {
    let mut addr_to_id = HashMap::new();
    let mut id_to_value = HashMap::new();

    // Register empty string
    let empty_fv = VALUE_EMPTY_STRING.unpack();
    let empty_id = hash_empty_string();
    addr_to_id.insert(empty_fv.ptr_value().ptr_value_untagged(), empty_id);
    id_to_value.insert(empty_id, empty_fv);

    // Register single ASCII character strings (0x00 to 0x7F)
    for (i, repr) in VALUE_BYTE_STRINGS.iter().enumerate() {
        let fv = repr.unpack();
        let id = hash_short_string(i as u8);
        addr_to_id.insert(fv.ptr_value().ptr_value_untagged(), id);
        id_to_value.insert(id, fv);
    }

    StaticStringMaps {
        addr_to_id,
        id_to_value,
    }
});
