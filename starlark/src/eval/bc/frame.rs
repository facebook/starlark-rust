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

//! Local variables and stack, in single allocation.

use std::{cell::Cell, mem, mem::MaybeUninit, ptr, slice};

use crate::{
    eval::{
        bc::{if_debug::IfDebug, stack_ptr::BcStackPtr},
        runtime::slots::LocalSlotId,
        Evaluator,
    },
    values::{Trace, Tracer, Value},
};

/// Current `def` frame (but not native function frame).
///
/// We erase lifetime here, because it is very hard to do lifetimes properly.
pub(crate) struct BcFrame<'v> {
    /// Pointer to the locals followed by stack.
    ptr: *mut Option<Value<'v>>,
    /// Number of local slots.
    local_count: u32,
    /// Number of stack slots.
    max_stack_size: u32,
    /// Current stack pointer.
    stack_ptr_if_debug: IfDebug<*mut Value<'v>>,
}

impl<'v> Default for BcFrame<'v> {
    fn default() -> Self {
        Self {
            ptr: ptr::null_mut(),
            local_count: 0,
            max_stack_size: 0,
            stack_ptr_if_debug: IfDebug::new(ptr::null_mut()),
        }
    }
}

impl<'v> BcFrame<'v> {
    /// Is this frame allocated or constructed empty?
    pub(crate) fn is_inititalized(&self) -> bool {
        !self.ptr.is_null()
    }

    pub(crate) fn max_stack_size(&self) -> u32 {
        self.max_stack_size
    }

    #[inline(always)]
    pub(crate) fn locals(&self) -> &[Cell<Option<Value<'v>>>] {
        debug_assert!(self.is_inititalized());
        unsafe {
            slice::from_raw_parts(
                self.ptr as *const Cell<Option<Value>>,
                self.local_count as usize,
            )
        }
    }

    #[inline(always)]
    pub(crate) fn locals_mut(&mut self) -> &mut [Option<Value<'v>>] {
        debug_assert!(self.is_inititalized());
        unsafe { slice::from_raw_parts_mut(self.ptr, self.local_count as usize) }
    }

    #[inline(always)]
    pub(crate) fn stack_bottom_ptr<'a>(&self) -> BcStackPtr<'v, 'a> {
        debug_assert!(self.is_inititalized());
        unsafe {
            // Here we (incorrectly) drop lifetime of self.
            // We need to do it, because we need `&mut Evaluator`
            // after stack pointer is acquired.
            BcStackPtr::new(slice::from_raw_parts_mut(
                self.ptr.add(self.local_count as usize) as *mut _,
                self.max_stack_size as usize,
            ))
        }
    }

    #[inline(always)]
    pub(crate) fn set_stack_ptr_if_debug(&mut self, ptr: &BcStackPtr<'v, '_>) {
        self.stack_ptr_if_debug.set(ptr.ptr());
    }

    /// Assert there are no values on the stack.
    #[inline(always)]
    pub(crate) fn debug_assert_stack_size_if_zero(&self) {
        debug_assert!(*self.stack_ptr_if_debug.get_ref_if_debug() == self.stack_bottom_ptr().ptr());
    }

    /// Gets a local variable. Returns None to indicate the variable is not yet assigned.
    #[inline(always)]
    pub(crate) fn get_slot(&self, slot: LocalSlotId) -> Option<Value<'v>> {
        debug_assert!(self.is_inititalized());
        debug_assert!(slot.0 < self.local_count);
        unsafe { self.ptr.add(slot.0 as usize).read() }
    }

    #[inline(always)]
    pub(crate) fn set_slot(&self, slot: LocalSlotId, value: Value<'v>) {
        debug_assert!(self.is_inititalized());
        debug_assert!(slot.0 < self.local_count);
        unsafe { self.ptr.add(slot.0 as usize).write(Some(value)) }
    }
}

unsafe impl<'v> Trace<'v> for BcFrame<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.locals_mut().trace(tracer);
        // Note this does not trace the stack.
        // GC can be performed only when the stack is empty.
        self.debug_assert_stack_size_if_zero();
    }
}

/// Allocate a frame and store it in the evaluator.
///
/// After callback finishes, previous frame is restored.
#[inline(always)]
pub(crate) fn alloca_frame<'v, R>(
    eval: &mut Evaluator<'v, '_>,
    local_count: u32,
    max_stack_size: u32,
    k: impl FnOnce(&mut Evaluator<'v, '_>) -> R,
) -> R {
    eval.alloca_uninit::<Option<Value>, _, _>(
        (local_count as usize) + (max_stack_size as usize),
        |locals_and_stack, eval| {
            let (locals, _stack) = locals_and_stack.split_at_mut(local_count as usize);
            // TODO(nga): no need to fill the slots for parameters.
            locals.fill(MaybeUninit::new(None));
            let frame = BcFrame {
                ptr: locals.as_mut_ptr() as *mut _,
                local_count,
                max_stack_size,
                stack_ptr_if_debug: IfDebug::new(unsafe {
                    locals.as_mut_ptr().add(local_count as usize)
                } as *mut _),
            };
            let old_frame = mem::replace(&mut eval.current_frame, frame);
            let r = k(eval);
            eval.current_frame = old_frame;
            r
        },
    )
}
