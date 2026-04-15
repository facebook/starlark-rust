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
use pagable::PagableCursor;
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

use crate::values::layout::pointer::PointerTags;
use crate::values::layout::vtable::AValueVTable;
use crate::values::layout::vtable::StarlarkValueRawPtr;

/// A slot in the arena waiting to be deserialized.
/// Contains all info needed to locate and deserialize a single value.
pub(crate) struct ValueDeserSlot {
    /// Byte offset of this value's data relative to base_pos.
    stream_offset: u32,
    /// Arc index offset relative to base_pos.arc_index.
    arc_offset: u32,
    /// This value's vtable, used for deserialization dispatch.
    vtable: &'static AValueVTable,
    /// Raw pointer to the pre-allocated header in the arena.
    raw_ptr: StarlarkValueRawPtr,
    /// Whether this value has been deserialized.
    initialized: bool,
}

impl ValueDeserSlot {
    pub(crate) fn new(
        stream_offset: u32,
        arc_offset: u32,
        vtable: &'static AValueVTable,
        raw_ptr: StarlarkValueRawPtr,
    ) -> Self {
        Self {
            stream_offset,
            arc_offset,
            vtable,
            raw_ptr,
            initialized: false,
        }
    }
}

/// Info returned by `try_claim` — everything the caller needs to deserialize a value.
pub(crate) struct DeserializeRecipe {
    /// Absolute cursor position of this value's data.
    pub(crate) abs_pos: PagableCursor,
    /// Vtable for deserialization dispatch.
    pub(crate) vtable: &'static AValueVTable,
    /// Raw pointer to the pre-allocated header in the arena.
    pub(crate) raw_ptr: StarlarkValueRawPtr,
}

/// Tracks deserialization state for all values in a heap.
/// Acts as a work queue — each value can be "claimed" for deserialization exactly once.
pub(crate) struct HeapDeserializationState {
    /// All values in this heap.
    slots: Vec<ValueDeserSlot>,
    /// Map from header pointer address to slot index.
    ptr_to_index: HashMap<usize, usize>,
    /// Absolute cursor position of value data start (base for relative offsets).
    base_pos: PagableCursor,
    /// Absolute cursor position past all value data (from the offset table end sentinel).
    end_pos: PagableCursor,
}

impl HeapDeserializationState {
    pub(crate) fn new(
        slots: Vec<ValueDeserSlot>,
        ptr_to_index: HashMap<usize, usize>,
        base_pos: PagableCursor,
        end_pos: PagableCursor,
    ) -> Self {
        Self {
            slots,
            ptr_to_index,
            base_pos,
            end_pos,
        }
    }

    /// Number of values in this heap.
    pub(crate) fn value_count(&self) -> usize {
        self.slots.len()
    }

    /// Look up a value index by a FrozenValue that points into this heap.
    /// Returns None for inline ints, unfrozen pointers, or pointers not in this heap.
    pub(crate) fn find_by_frozen_value(&self, fv: FrozenValue) -> Option<usize> {
        match fv.ptr_value().tags() {
            PointerTags::OtherFrozen | PointerTags::StrFrozen => {
                let ptr_addr = fv.ptr_value().ptr_value_untagged();
                self.ptr_to_index.get(&ptr_addr).copied()
            }
            _ => None,
        }
    }

    /// Try to claim a value for deserialization.
    /// If not yet initialized, marks it and returns the info needed to deserialize.
    /// If already initialized, returns None.
    pub(crate) fn try_claim(&mut self, index: usize) -> Option<DeserializeRecipe> {
        let slot = &mut self.slots[index];
        if slot.initialized {
            return None;
        }
        slot.initialized = true;
        Some(DeserializeRecipe {
            abs_pos: PagableCursor {
                byte_pos: self.base_pos.byte_pos + slot.stream_offset as usize,
                arc_index: self.base_pos.arc_index + slot.arc_offset as usize,
            },
            vtable: slot.vtable,
            raw_ptr: slot.raw_ptr,
        })
    }

    /// Absolute cursor position past all value data (from the offset table end sentinel).
    pub(crate) fn end_position(&self) -> PagableCursor {
        self.end_pos
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
    /// Current heap value tracking for ensure_initialized.
    current_heap_deser_state: HeapDeserializationState,
}

impl<'a, 'de> StarlarkDeserializerImpl<'a, 'de> {
    /// Create a new deserializer with shared state and current heap id.
    pub(crate) fn new(
        pagable: &'a mut dyn PagableDeserializer<'de>,
        state: Arc<Mutex<StarlarkDeserState>>,
        current_heap_id: HeapRefId,
        current_heap_deser_state: HeapDeserializationState,
    ) -> Self {
        Self {
            pagable,
            state,
            current_heap_id: Some(current_heap_id),
            current_heap_deser_state,
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

    pub(crate) fn current_heap_deser_state(&mut self) -> &HeapDeserializationState {
        &self.current_heap_deser_state
    }

    pub(crate) fn current_heap_deser_state_mut(&mut self) -> &mut HeapDeserializationState {
        &mut self.current_heap_deser_state
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

    fn ensure_initialized(&mut self, fv: FrozenValue) -> crate::Result<()> {
        let idx = match self.current_heap_deser_state().find_by_frozen_value(fv) {
            Some(idx) => idx,
            None => return Ok(()),
        };

        let target = match self.current_heap_deser_state_mut().try_claim(idx) {
            Some(target) => target,
            None => return Ok(()), // Already initialized.
        };

        let saved_pos = self.pagable.position();
        // SAFETY: abs_pos points to the start of this value's serialized data
        // (from the offset table). saved_pos is restored after deserialization.
        unsafe { self.pagable.seek(target.abs_pos) };
        (target.vtable.starlark_deserialize)(target.raw_ptr, self)?;
        unsafe { self.pagable.seek(saved_pos) };

        Ok(())
    }
}
