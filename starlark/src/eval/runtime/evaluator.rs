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

use crate::{
    codemap::{CodeMap, FileSpan, Span},
    collections::alloca::Alloca,
    environment::{
        slots::ModuleSlotId, EnvironmentError, FrozenModuleData, FrozenModuleValue, Globals, Module,
    },
    errors::{Diagnostic, Frame},
    eval::{
        runtime::{
            call_stack::CallStack,
            flame_profile::FlameProfile,
            heap_profile::HeapProfile,
            slots::{LocalSlotId, LocalSlots},
            stmt_profile::StmtProfile,
        },
        FileLoader,
    },
    values::{
        value_captured_get, FrozenHeap, Heap, Trace, Tracer, Value, ValueCaptured, ValueLike,
    },
};
use gazebo::{any::AnyLifetime, cast};
use once_cell::sync::Lazy;
use std::{
    cell::Cell,
    intrinsics::unlikely,
    mem::{self, MaybeUninit},
    path::Path,
};
use thiserror::Error;

#[derive(Error, Debug)]
#[allow(clippy::enum_variant_names)]
enum EvaluatorError {
    #[error("Can't call `write_heap_profile` unless you first call `enable_heap_profile`.")]
    HeapProfilingNotEnabled,
    #[error("Can't call `write_stmt_profile` unless you first call `enable_stmt_profile`.")]
    StmtProfilingNotEnabled,
    #[error("Can't call `write_flame_profile` unless you first call `enable_flame_profile`.")]
    FlameProfilingNotEnabled,
}

/// Number of bytes to allocate between GC's.
pub(crate) const GC_THRESHOLD: usize = 100000;

/// Holds everything about an ongoing evaluation (local variables, globals, module resolution etc).
pub struct Evaluator<'v, 'a> {
    // The module that is being used for this evaluation
    pub(crate) module_env: &'v Module,
    // The module-level variables in scope at the moment.
    // If `None` then we're in the initial module, use variables from `module_env`.
    // If `Some` we've called a `def` in a loaded frozen module.
    pub(crate) module_variables: Option<(&'static FrozenModuleData, FrozenModuleValue)>,
    // Local variables for this function, and older stack frames too.
    pub(crate) local_variables: LocalSlots<'v>,
    // Globals used to resolve global variables.
    pub(crate) globals: &'a Globals,
    // How we deal with a `load` function.
    pub(crate) loader: Option<&'a dyn FileLoader>,
    // The codemap that corresponds to this module.
    pub(crate) codemap: &'v CodeMap,
    // Should we enable heap profiling or not
    pub(crate) heap_profile: HeapProfile,
    // Should we enable flame profiling or not
    pub(crate) flame_profile: FlameProfile<'v>,
    // Is either heap or flame profiling enabled
    pub(crate) heap_or_flame_profile: bool,
    // Is GC disabled for some reason
    pub(crate) disable_gc: bool,
    // Size of the heap when we should next perform a GC.
    pub(crate) next_gc_level: usize,
    // Extra functions to run on each statement, usually empty
    pub(crate) before_stmt: Vec<&'a dyn Fn(Span, &mut Evaluator<'v, 'a>)>,
    // Used for line profiling
    stmt_profile: StmtProfile,
    // Used for stack-like allocation
    alloca: Alloca,
    /// Field that can be used for any purpose you want (can store types you define).
    /// Typically accessed via native functions you also define.
    pub extra: Option<&'a dyn AnyLifetime<'a>>,
    /// Field that can be used for any purpose you want (can store heap-resident [`Value<'v>`]).
    /// If this value is used, garbage collection is disabled.
    pub extra_v: Option<&'a dyn AnyLifetime<'v>>,
    // The Starlark-level call-stack of functions.
    // Must go last because it's quite a big structure
    pub(crate) call_stack: CallStack<'v>,
}

unsafe impl<'v> Trace<'v> for Evaluator<'v, '_> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        let mut roots = self.module_env.slots().get_slots_mut();
        roots.trace(tracer);
        self.local_variables.trace(tracer);
        self.call_stack.trace(tracer);
        self.flame_profile.trace(tracer);
    }
}

impl<'v, 'a> Evaluator<'v, 'a> {
    /// Crate a new [`Evaluator`] specifying the [`Module`] used for module variables,
    /// and the [`Globals`] used to resolve global variables.
    ///
    /// If your program contains `load()` statements, you also need to call
    /// [`set_loader`](Evaluator::set_loader).
    pub fn new(module: &'v Module, globals: &'a Globals) -> Self {
        static CODEMAP: Lazy<CodeMap> = Lazy::new(CodeMap::default);

        module.frozen_heap().add_reference(globals.heap());
        Evaluator {
            call_stack: CallStack::default(),
            module_env: module,
            module_variables: None,
            local_variables: LocalSlots::new(),
            globals,
            loader: None,
            codemap: &CODEMAP, // Will be replaced before it is used
            extra: None,
            extra_v: None,
            next_gc_level: GC_THRESHOLD,
            disable_gc: false,
            alloca: Alloca::new(),
            heap_profile: HeapProfile::new(),
            stmt_profile: StmtProfile::new(),
            flame_profile: FlameProfile::new(),
            heap_or_flame_profile: false,
            before_stmt: Vec::new(),
        }
    }

    /// Disables garbage collection from now onwards. Cannot be re-enabled.
    /// Usually called because you have captured [`Value`]'s unsafely, either in
    /// global variables or the [`extra`](Evaluator::extra) field.
    pub fn disable_gc(&mut self) {
        self.disable_gc = true;
    }

    /// Set the [`FileLoader`] used to resolve `load()` statements.
    /// A list of all load statements can be obtained through
    /// [`AstModule::loads`](crate::syntax::AstModule::loads).
    pub fn set_loader(&mut self, loader: &'a dyn FileLoader) {
        self.loader = Some(loader);
    }

    /// Enable profiling, allowing [`Evaluator::write_heap_profile`] to be used.
    /// Has the side effect of disabling garbage-collection.
    ///
    /// Starlark contains three types of profile information - `heap`, `stmt` and `flame`.
    /// These must be enabled _before_ execution with [`enable_heap_profile`](Evaluator::enable_heap_profile)/
    /// [`enable_stmt_profile`](Evaluator::enable_stmt_profile)/
    /// [`enable_flame_profile`](Evaluator::enable_flame_profile), then after execution the
    /// profiles can be written to a file using [`write_heap_profile`](Evaluator::write_heap_profile)/
    /// [`write_stmt_profile`](Evaluator::write_stmt_profile)/
    /// [`write_flame_profile`](Evaluator::write_flame_profile). These profiling modes both have
    /// some overhead, so while they _can_ be used simultaneously, it's usually better to run the
    /// code repeatedly if that's possible.
    ///
    /// * The `heap_profile` mode provides information about the time spent in each function and allocations
    ///   performed by each function. Enabling this mode the side effect of disabling garbage-collection.
    ///   This profiling mode is the recommended one.
    /// * The `stmt_profile` mode provides information about time spent in each statement.
    /// * The `flame_profile` mode provides input compatible with
    ///   [flamegraph.pl](https://github.com/brendangregg/FlameGraph/blob/master/flamegraph.pl).
    pub fn enable_heap_profile(&mut self) {
        self.heap_profile.enable();
        self.heap_or_flame_profile = true;
        // Disable GC because otherwise why lose the profile records, as we use the heap
        // to store a complete list of what happened in linear order.
        self.disable_gc = true;
    }

    /// Enable statement profiling, allowing [`Evaluator::write_stmt_profile`] to be used.
    /// See [`Evaluator::enable_heap_profile`] for details about the types of Starlark profiles.
    pub fn enable_stmt_profile(&mut self) {
        self.stmt_profile.enable();
        self.before_stmt(&|span, eval| eval.stmt_profile.before_stmt(span, eval.codemap));
    }

    /// Enable statement profiling, allowing [`Evaluator::write_flame_profile`] to be used.
    /// See [`Evaluator::enable_heap_profile`] for details about the types of Starlark profiles.
    pub fn enable_flame_profile(&mut self) {
        self.flame_profile.enable();
        self.heap_or_flame_profile = true;
    }

    /// Write a profile (as a `.csv` file) to a file.
    /// Only valid if [`enable_heap_profile`](Evaluator::enable_heap_profile) was called before execution began.
    /// See [`Evaluator::enable_heap_profile`] for details about the two types of Starlark profiles.
    pub fn write_heap_profile<P: AsRef<Path>>(&self, filename: P) -> anyhow::Result<()> {
        self.heap_profile
            .write(filename.as_ref(), self.heap())
            .unwrap_or_else(|| Err(EvaluatorError::HeapProfilingNotEnabled.into()))
    }

    /// Write a profile (as a `.csv` file) to a file.
    /// Only valid if [`enable_stmt_profile`](Evaluator::enable_stmt_profile) was called before execution began.
    /// See [`Evaluator::enable_heap_profile`] for details about two types of Starlark profiles.
    pub fn write_stmt_profile<P: AsRef<Path>>(&self, filename: P) -> anyhow::Result<()> {
        self.stmt_profile
            .write(filename.as_ref())
            .unwrap_or_else(|| Err(EvaluatorError::StmtProfilingNotEnabled.into()))
    }

    /// Write a profile to a file, suitable as input to
    /// [flamegraph.pl](https://github.com/brendangregg/FlameGraph/blob/master/flamegraph.pl).
    /// Only valid if [`enable_flame_profile`](Evaluator::enable_flame_profile) was called before execution began.
    /// See [`Evaluator::enable_heap_profile`] for details about the types of Starlark profiles.
    pub fn write_flame_profile<P: AsRef<Path>>(&self, filename: P) -> anyhow::Result<()> {
        self.flame_profile
            .write(filename.as_ref())
            .unwrap_or_else(|| Err(EvaluatorError::FlameProfilingNotEnabled.into()))
    }

    /// Obtain the current call-stack, suitable for use with [`Diagnostic`].
    pub fn call_stack(&self) -> Vec<Frame> {
        self.call_stack.to_diagnostic_frames()
    }

    /// Obtain the top location on the call-stack. May be [`None`] if the
    /// call happened via native functions.
    pub fn call_stack_top_location(&self) -> Option<FileSpan> {
        self.call_stack.top_location()
    }

    /// Called before every statement is run with the [`Span`] and a reference to the containing [`Evaluator`].
    /// A list of all possible statements can be obtained in advance by
    /// [`AstModule::stmt_locations`](crate::syntax::AstModule::stmt_locations).
    ///
    /// This function may have no effect is called mid evaluation.
    pub fn before_stmt(&mut self, f: &'a dyn Fn(Span, &mut Evaluator<'v, 'a>)) {
        self.before_stmt.push(f)
    }

    /// Given a [`Span`] resolve it to a concrete [`FileSpan`] using
    /// whatever module is currently at the top of the stack.
    /// This function can be used in conjunction with [`before_stmt`](Evaluator::before_stmt).
    pub fn file_span(&self, span: Span) -> FileSpan {
        self.codemap.file_span(span)
    }

    pub(crate) fn check_types(&self) -> bool {
        // We currently always check types. We suspect that for performance reasons one day
        // we'll want to make it optional, so guard the relevant places behind this test.
        true
    }

    /// An annotation that a function occurs within a name. Useful for profiling. Usually compiled away.
    #[inline(always)]
    pub fn ann<R>(&mut self, _name: &'static str, within: impl FnOnce(&mut Self) -> R) -> R {
        within(self)
    }

    /// Called to add an entry to the call stack, by the function being invoked.
    /// Called for all types of function, including those written in Rust.
    #[inline(always)]
    pub fn with_call_stack<R>(
        &mut self,
        function: Value<'v>,
        span: Option<Span>,
        within: impl FnOnce(&mut Self) -> anyhow::Result<R>,
    ) -> anyhow::Result<R> {
        #[cold]
        #[inline(never)]
        fn add_diagnostics(e: anyhow::Error, me: &Evaluator) -> anyhow::Error {
            Diagnostic::modify(e, |d: &mut Diagnostic| {
                // Make sure we capture the call_stack before popping things off it
                d.set_call_stack(|| me.call_stack.to_diagnostic_frames());
            })
        }

        self.call_stack.push(
            function,
            span.unwrap_or_default(),
            span.map(|_| self.codemap),
        )?;
        if unlikely(self.heap_or_flame_profile) {
            self.heap_profile.record_call_enter(function, self.heap());
            self.flame_profile.record_call_enter(function);
        }
        // Must always call .pop regardless
        let res = within(self).map_err(|e| add_diagnostics(e, self));
        self.call_stack.pop();
        if unlikely(self.heap_or_flame_profile) {
            self.heap_profile.record_call_exit(self.heap());
            self.flame_profile.record_call_exit();
        }
        res
    }

    pub(crate) fn set_codemap(&mut self, codemap: &'v CodeMap) -> &'v CodeMap {
        mem::replace(&mut self.codemap, codemap)
    }

    /// Called to change the local variables, from the callee.
    /// Only called for user written functions.
    #[inline(always)] // There is only one caller
    pub(crate) fn with_function_context<R>(
        &mut self,
        module: Option<FrozenModuleValue>, // None == use module_env
        codemap: &CodeMap,
        within: impl FnOnce(&mut Self) -> R,
    ) -> R {
        // Safe because we promise to put codemap back to how it was before this function terminates.
        // And because anyone who gets access to the CodeMap does so with a dupe, taking ownership.
        // We'd like to express that `Evaluator` has a lifetime for the codemap that lasts only
        // this function, but Rust can't express that.
        let codemap = unsafe { cast::ptr_lifetime(codemap) };

        // Capture the variables we will be mutating
        let old_codemap = self.set_codemap(codemap);

        // Set up for the new function call
        let old_module_variables =
            mem::replace(&mut self.module_variables, module.map(|x| (x.get(), x)));

        // Run the computation
        let res = within(self);

        // Restore them all back
        self.set_codemap(old_codemap);
        self.module_variables = old_module_variables;
        res
    }

    /// The active heap where [`Value`]s are allocated.
    pub fn heap(&self) -> &'v Heap {
        self.module_env.heap()
    }

    /// The frozen heap. It's possible to allocate [`FrozenValue`](crate::values::FrozenValue)s here,
    /// but often not a great idea, as they will remain allocated as long
    /// as the results of this execution are required.
    /// Suitable for use with [`add_reference`](FrozenHeap::add_reference)
    /// and [`OwnedFrozenValue::owned_frozen_value`](crate::values::OwnedFrozenValue::owned_frozen_value).
    pub fn frozen_heap(&self) -> &FrozenHeap {
        self.module_env.frozen_heap()
    }

    pub(crate) fn get_slot_module(&self, slot: ModuleSlotId) -> anyhow::Result<Value<'v>> {
        // Make sure the error-path doesn't get inlined into the normal-path execution
        #[cold]
        #[inline(never)]
        fn error<'v>(eval: &Evaluator<'v, '_>, slot: ModuleSlotId) -> anyhow::Error {
            let name = match &eval.module_variables {
                None => eval.module_env.names().get_slot(slot),
                Some(e) => e.0.get_slot_name(slot),
            }
            .unwrap_or_else(|| "<unknown>".to_owned());
            EnvironmentError::LocalVariableReferencedBeforeAssignment(name).into()
        }

        match &self.module_variables {
            None => self.module_env.slots().get_slot(slot),
            Some(e) => e.0.get_slot(slot).map(Value::new_frozen),
        }
        .ok_or_else(|| error(self, slot))
    }

    // Make sure the error-path doesn't get inlined into the normal-path execution
    #[cold]
    #[inline(never)]
    fn local_var_referenced_before_assignment(name: &str) -> anyhow::Error {
        EnvironmentError::LocalVariableReferencedBeforeAssignment(name.to_owned()).into()
    }

    pub(crate) fn get_slot_local(
        &self,
        slot: LocalSlotId,
        name: &str,
    ) -> anyhow::Result<Value<'v>> {
        self.local_variables
            .get_slot(slot)
            .ok_or_else(|| Self::local_var_referenced_before_assignment(name))
    }

    pub(crate) fn get_slot_local_captured(
        &self,
        slot: LocalSlotId,
        name: &str,
    ) -> anyhow::Result<Value<'v>> {
        let value_captured = self.get_slot_local(slot, name)?;
        let value_captured = value_captured_get(value_captured);
        value_captured.ok_or_else(|| Self::local_var_referenced_before_assignment(name))
    }

    pub(crate) fn clone_slot_capture(&self, slot: LocalSlotId) -> Value<'v> {
        match self.local_variables.get_slot(slot) {
            Some(value_captured) => {
                debug_assert!(
                    value_captured.downcast_ref::<ValueCaptured>().is_some(),
                    "slot {:?} is expected to be ValueCaptured, it is {:?} ({})",
                    slot,
                    value_captured,
                    value_captured.get_type()
                );
                value_captured
            }
            None => {
                let value_captured = self.heap().alloc_complex(ValueCaptured(Cell::new(None)));
                self.local_variables.set_slot(slot, value_captured);
                value_captured
            }
        }
    }

    /// Set a variable in the top-level module currently being processed.
    /// This may not be the module the function is being called in.
    ///
    /// Any variables which are set will be available in the [`Module`] after evaluation returns.
    /// If those variables are _also_ existing top-level variables, then the program from that point on
    /// will incorporate those values. If they aren't existing top-level variables, they will be ignored.
    /// These details are subject to change.
    /// As such, use this API with a healthy dose of caution and in limited settings.
    pub fn set_module_variable_at_some_point(
        &mut self,
        name: &str,
        value: Value<'v>,
    ) -> anyhow::Result<()> {
        value.export_as(name, self);
        self.module_env.set(name, value);
        Ok(())
    }

    pub(crate) fn set_slot_module(&mut self, slot: ModuleSlotId, value: Value<'v>) {
        self.module_env.slots().set_slot(slot, value);
    }

    pub(crate) fn set_slot_local(&mut self, slot: LocalSlotId, value: Value<'v>) {
        self.local_variables.set_slot(slot, value)
    }

    pub(crate) fn set_slot_local_captured(&mut self, slot: LocalSlotId, value: Value<'v>) {
        match self.local_variables.get_slot(slot) {
            Some(value_captured) => {
                let value_captured = value_captured
                    .downcast_ref::<ValueCaptured>()
                    .expect("not a ValueCaptured");
                value_captured.set(value);
            }
            None => {
                let value_captured = self
                    .heap()
                    .alloc_complex(ValueCaptured(Cell::new(Some(value))));
                self.local_variables.set_slot(slot, value_captured);
            }
        };
    }

    /// Take a value from the local slot and store it back wrapped in [`ValueCaptured`].
    pub(crate) fn wrap_local_slot_captured(&mut self, slot: LocalSlotId) {
        let value = self.local_variables.get_slot(slot).expect("slot unset");
        debug_assert!(value.downcast_ref::<ValueCaptured>().is_none());
        let value_captured = self
            .heap()
            .alloc_complex(ValueCaptured(Cell::new(Some(value))));
        self.local_variables.set_slot(slot, value_captured);
    }

    /// Cause a GC to be triggered next time it's possible.
    pub(crate) fn trigger_gc(&mut self) {
        // We will GC next time we can, since the threshold is if 0 or more bytes are allocated
        self.next_gc_level = 0;
    }

    /// Perform a garbage collection.
    /// After this operation all [`Value`]s not reachable from the evaluator will be invalid,
    /// and using them will lead to a segfault.
    /// Do not call during Starlark evaluation.
    pub unsafe fn garbage_collect(&mut self) {
        self.heap().garbage_collect(|tracer| self.trace(tracer))
    }

    /// Note that the `Drop` for the `T` will not be called. That's safe if there is no `Drop`,
    /// or you call it yourself.
    #[inline(always)]
    pub(crate) fn alloca_uninit<T, R>(
        &mut self,
        len: usize,
        f: impl FnOnce(&mut [MaybeUninit<T>], &mut Self) -> R,
    ) -> R {
        // We want to be able to access the evaluator underneath the alloca.
        // We know that the alloca will be used in a stacked way, so that's fine.
        let alloca = unsafe { cast::ptr_lifetime(&self.alloca) };
        alloca.alloca_uninit(len, |xs| f(xs, self))
    }
}
