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

//! Implementation of StarlarkDeserializeContext.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;

use dupe::Dupe;
use pagable::PagableDeserialize;
use pagable::PagableDeserializer;

use crate::pagable::error::PagableError;
use crate::pagable::heap_ref_id::HeapRefId;
use crate::pagable::serialized_frozen_value::SerializedFrozenValue;
use crate::pagable::starlark_deserialize::StarlarkDeserializeContext;
use crate::values::FrozenValue;
use crate::values::layout::heap::arena::ArenaOffset;
use crate::values::layout::heap::arena::BumpKind;
use crate::values::layout::heap::repr::AValueHeader;
use crate::values::types::int::inline_int::InlineInt;

/// Bump base addresses for a deserialized heap.
struct HeapBumpBases {
    drop_base: usize,
    non_drop_base: usize,
}

impl HeapBumpBases {
    /// Resolve an `ArenaOffset` to a raw pointer address.
    fn resolve(&self, offset: &ArenaOffset) -> usize {
        let base = match offset.bump {
            BumpKind::Drop => self.drop_base,
            BumpKind::NonDrop => self.non_drop_base,
        };
        base + offset.offset as usize
    }
}

/// Shared deserialization state across all heaps deserialized in a session.
/// Stored in `SessionContext` as `Arc<Mutex<StarlarkDeserState>>` so that
/// independently-deserialized heaps (via pagable arcs) can all register
/// their base addresses and resolve cross-heap references.
pub(crate) struct StarlarkDeserState {
    /// Bump bases for each deserialized heap, keyed by HeapRefId.
    heap_bases: HashMap<HeapRefId, HeapBumpBases>,
}

impl StarlarkDeserState {
    pub(crate) fn new() -> Self {
        Self {
            heap_bases: HashMap::new(),
        }
    }

    /// Register a heap's base addresses.
    pub(crate) fn register_bases(
        &mut self,
        heap_id: HeapRefId,
        drop_base: usize,
        non_drop_base: usize,
    ) {
        self.heap_bases.insert(
            heap_id,
            HeapBumpBases {
                drop_base,
                non_drop_base,
            },
        );
    }
}

/// Concrete implementation of StarlarkDeserializeContext.
///
/// Wraps a `PagableDeserializer` and a shared `StarlarkDeserState` to provide
/// FrozenValue deserialization with same-heap and cross-heap reference resolution.
pub struct StarlarkDeserializerImpl<'a, 'de> {
    pagable: &'a mut dyn PagableDeserializer<'de>,
    /// Shared state for cross-heap base lookups.
    state: Arc<Mutex<StarlarkDeserState>>,
    /// The HeapRefId of the heap currently being deserialized.
    current_heap_id: Option<HeapRefId>,
}

impl<'a, 'de> StarlarkDeserializerImpl<'a, 'de> {
    /// Create a new deserializer with shared state and current heap id.
    pub(crate) fn new(
        pagable: &'a mut dyn PagableDeserializer<'de>,
        state: Arc<Mutex<StarlarkDeserState>>,
        current_heap_id: HeapRefId,
    ) -> Self {
        Self {
            pagable,
            state,
            current_heap_id: Some(current_heap_id),
        }
    }

    /// Get or create the shared `StarlarkDeserState` from the deserializer's `SessionContext`.
    pub(crate) fn get_or_create_state(
        deserializer: &mut dyn PagableDeserializer<'_>,
    ) -> Arc<Mutex<StarlarkDeserState>> {
        let mut ctx = deserializer
            .session_context()
            .lock()
            .expect("session context lock poisoned");
        if let Some(state) = ctx.get::<Arc<Mutex<StarlarkDeserState>>>() {
            return state.dupe();
        }
        let state = Arc::new(Mutex::new(StarlarkDeserState::new()));
        ctx.set(state.dupe());
        state
    }
}

impl<'de> StarlarkDeserializeContext<'de> for StarlarkDeserializerImpl<'_, 'de> {
    fn pagable(&mut self) -> &mut dyn PagableDeserializer<'de> {
        self.pagable
    }

    fn deserialize_frozen_value(&mut self) -> crate::Result<FrozenValue> {
        let serialized = SerializedFrozenValue::pagable_deserialize(self.pagable)?;
        let state = self.state.lock().expect("deser state lock poisoned");
        match serialized {
            SerializedFrozenValue::SameHeapPtr { offset, is_str } => {
                let heap_id = self
                    .current_heap_id
                    .ok_or(PagableError::NoCurrentHeapContext)?;
                let bases = state
                    .heap_bases
                    .get(&heap_id)
                    .ok_or(PagableError::HeapBasesNotRegistered)?;
                let ptr = bases.resolve(&offset);
                let header = unsafe { &*(ptr as *const AValueHeader) };
                Ok(FrozenValue::new_ptr(header, is_str))
            }
            SerializedFrozenValue::CrossHeapPtr {
                heap_id,
                offset,
                is_str,
            } => {
                let bases = state
                    .heap_bases
                    .get(&heap_id)
                    .ok_or(PagableError::CrossHeapBasesNotRegistered { heap_id })?;
                let ptr = bases.resolve(&offset);
                let header = unsafe { &*(ptr as *const AValueHeader) };
                Ok(FrozenValue::new_ptr(header, is_str))
            }
            SerializedFrozenValue::InlineInt(v) => {
                let inline = InlineInt::try_from(v)
                    .map_err(|_| anyhow::anyhow!("Integer {} does not fit in InlineInt", v))?;
                Ok(FrozenValue::new_int(inline))
            }
        }
    }
}
