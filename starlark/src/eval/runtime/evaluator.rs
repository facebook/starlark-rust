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
    codemap::{CodeMap, Span, SpanLoc},
    collections::stack::Stack1,
    environment::{
        slots::LocalSlots, EnvironmentError, FrozenModuleRef, FrozenModuleValue, Globals, Module,
    },
    errors::{Diagnostic, Frame},
    eval::{
        runtime::{call_stack::CallStack, stmt_profile::StmtProfile},
        FileLoader,
    },
    values::{FrozenHeap, Heap, Value, ValueRef, Walker},
};
use gazebo::any::AnyLifetime;
use std::{mem, path::Path};
use thiserror::Error;

#[derive(Error, Debug)]
enum EvaluatorError {
    #[error("Can't call `write_profile` unless you first call `enable_profile`.")]
    ProfilingNotEnabled,
    #[error("Can't call `write_stmt_profile` unless you first call `enable_stmt_profile`.")]
    StmtProfilingNotEnabled,
}

/// Holds everything about an ongoing evaluation (local variables, globals, module resolution etc).
pub struct Evaluator<'v, 'a> {
    // Am I at the root module-level, true until a function call
    pub(crate) is_module_scope: bool,
    // The module that is being used for this evaluation
    pub(crate) module_env: &'v Module,
    // The module-level variables in scope at the moment.
    // If `None` then we're in the initial module, use variables from `module_env`.
    // If `Some` we've called a `def` in a loaded frozen module.
    pub(crate) module_variables: Option<FrozenModuleRef>,
    // Local variables for this function, and older stack frames too.
    pub(crate) local_variables: Stack1<LocalSlots<'v>>,
    // Globals used to resolve global variables.
    pub(crate) globals: &'a Globals,
    // The Starlark-level call-stack of functions.
    pub(crate) call_stack: CallStack<'v>,
    // How we deal with a `load` function.
    pub(crate) loader: Option<&'a mut dyn FileLoader>,
    // The codemap that corresponds to this module.
    pub(crate) codemap: CodeMap,
    // Should we enable profiling or not
    pub(crate) profiling: bool,
    // Is GC disabled for some reason
    pub(crate) disable_gc: bool,
    // Size of the heap when we last performed a GC
    pub(crate) last_heap_size: usize,
    // The normal heap, where values are produced, get GC'd at the end
    pub(crate) heap: &'v Heap,
    // Should we do runtime checking of types (defaults to true)
    pub(crate) check_types: bool,
    // Extra functions to run on each statement, usually empty
    pub(crate) before_stmt: Vec<&'a dyn Fn(Span, &mut Evaluator<'v, 'a>)>,
    // Used for line profiling
    stmt_profile: StmtProfile,
    /// Field that can be used for any purpose you want (can store types you define).
    /// Typically accessed via native functions you also define.
    pub extra: Option<&'a dyn AnyLifetime<'a>>,
    /// Field that can be used for any purpose you want (can store heap-resident [`Value<'v>`]).
    /// If this value is used, garbage collection is disabled.
    pub extra_v: Option<&'a dyn AnyLifetime<'v>>,
}
impl<'v, 'a> Evaluator<'v, 'a> {
    /// Crate a new [`Evaluator`] specifying the [`Module`] used for module variables,
    /// and the [`Globals`] used to resolve global variables.
    ///
    /// If your program contains `load()` statements, you also need to call
    /// [`set_loader`](Evaluator::set_loader).
    pub fn new(module: &'v Module, globals: &'a Globals) -> Self {
        module.frozen_heap().add_reference(globals.heap());
        Evaluator {
            call_stack: CallStack::default(),
            is_module_scope: true,
            module_env: module,
            module_variables: None,
            local_variables: Stack1::default(),
            globals,
            loader: None,
            codemap: CodeMap::default(), // Will be replaced before it is used
            extra: None,
            extra_v: None,
            last_heap_size: 0,
            disable_gc: false,
            profiling: false,
            check_types: true,
            stmt_profile: StmtProfile::new(),
            heap: module.heap(),
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
    pub fn set_loader(&mut self, loader: &'a mut dyn FileLoader) {
        self.loader = Some(loader);
    }

    /// Enable profiling, allowing [`Evaluator::write_profile`] to be used.
    /// Has the side effect of disabling garbage-collection.
    ///
    /// Starlark contains two types of profile information - `profile` and `stmt_profile`.
    /// These must be enabled _before_ execution with [`enable_profile`](Evaluator::enable_profile)/
    /// [`enable_stmt_profile`](Evaluator::enable_stmt_profile), then after execution the
    /// profiles can be written to a file using [`write_profile`](Evaluator::write_profile)/
    /// [`write_stmt_profile`](Evaluator::write_stmt_profile). These profiling modes both have
    /// some overhead, so while they _can_ be used simultaneously, it's usually better to run the
    /// code twice if that's possible.
    ///
    /// * The `profile` mode provides information about the time spent in each function and allocations
    ///   performed by each function. Enabling this mode the side effect of disabling garbage-collection.
    ///   This profiling mode is the recommended one.
    /// * The `stmt_profile` mode provides information about time spent in each statement.
    pub fn enable_profile(&mut self) {
        self.profiling = true;
        // Disable GC because otherwise why lose the profile records, as we use the heap
        // to store a complete list of what happened in linear order.
        self.disable_gc = true;
    }

    /// Enable statement profiling, allowing [`Evaluator::write_stmt_profile`] to be used.
    /// See [`Evaluator::enable_profile`] for details about the two types of Starlark profiles.
    pub fn enable_stmt_profile(&mut self) {
        self.stmt_profile.enable();
        self.before_stmt(&|span, evaluator| evaluator.stmt_profile.before_stmt(span));
    }

    /// Write a profile (as a `.csv` file) to a file.
    /// Only valid if [`enable_profile`](Evaluator::enable_profile) was called before execution began.
    /// See [`Evaluator::enable_profile`] for details about the two types of Starlark profiles.
    pub fn write_profile<P: AsRef<Path>>(&self, filename: P) -> anyhow::Result<()> {
        if !self.profiling {
            return Err(EvaluatorError::ProfilingNotEnabled.into());
        }
        self.heap.write_profile(filename.as_ref())
    }

    /// Write a profile (as a `.csv` file) to a file.
    /// Only valid if [`enable_stmt_profile`](Evaluator::enable_stmt_profile) was called before execution began.
    /// See [`Evaluator::enable_profile`] for details about the two types of Starlark profiles.
    pub fn write_stmt_profile<P: AsRef<Path>>(&self, filename: P) -> anyhow::Result<()> {
        self.stmt_profile
            .write(filename.as_ref())
            .unwrap_or_else(|| Err(EvaluatorError::StmtProfilingNotEnabled.into()))
    }

    /// Obtain the current call-stack, suitable for use with [`Diagnostic`].
    pub fn call_stack(&self) -> Vec<Frame> {
        self.call_stack.to_diagnostic_frames()
    }

    /// Obtain the top location on the call-stack. May be [`None`] if the
    /// call happened via native functions.
    pub fn call_stack_top_location(&self) -> Option<SpanLoc> {
        self.call_stack.top_location()
    }

    /// Called before every statement is run with the [`Span`] and a reference to the containing [`Evaluator`].
    /// A list of all possible statements can be obtained in advance by
    /// [`AstModule::stmt_locations`](crate::syntax::AstModule::stmt_locations).
    pub fn before_stmt(&mut self, f: &'a dyn Fn(Span, &mut Evaluator<'v, 'a>)) {
        self.before_stmt.push(f)
    }

    /// Given a [`Span`] resolve it to a concrete [`SpanLoc`] using
    /// whatever module is currently at the top of the stack.
    /// This function can be used in conjunction with [`before_stmt`](Evaluator::before_stmt).
    pub fn look_up_span(&self, span: Span) -> SpanLoc {
        self.codemap.look_up_span(span)
    }

    /// Called to add an entry to the call stack, from the caller.
    /// Called for all types of function (including those written in Rust)
    pub(crate) fn with_call_stack<R>(
        &mut self,
        function: Value<'v>,
        location: Option<(CodeMap, Span)>,
        within: impl FnOnce(&mut Self) -> anyhow::Result<R>,
    ) -> anyhow::Result<R> {
        self.call_stack.push(function, location)?;
        if self.profiling {
            self.heap.record_call_enter(function);
        }
        // Must always call .pop regardless
        let res = within(self).map_err(|e| {
            Diagnostic::modify(e, |d: &mut Diagnostic| {
                // Make sure we capture the call_stack before popping things off it
                d.set_call_stack(|| self.call_stack.to_diagnostic_frames());
            })
        });
        self.call_stack.pop();
        if self.profiling {
            self.heap.record_call_exit();
        }
        res
    }

    pub(crate) fn set_codemap(&mut self, codemap: CodeMap) -> CodeMap {
        self.stmt_profile.set_codemap(&codemap);
        mem::replace(&mut self.codemap, codemap)
    }

    /// Called to change the local variables, from the callee.
    /// Only called for user written functions.
    pub(crate) fn with_function_context<R, E>(
        &mut self,
        module: Option<FrozenModuleValue>, // None == use module_env
        locals: LocalSlots<'v>,
        codemap: CodeMap,
        within: impl FnOnce(&mut Self) -> Result<R, E>,
    ) -> Result<R, E>
    where
        E: From<anyhow::Error>,
    {
        // Capture the variables we will be mutating
        let old_is_module_scope = self.is_module_scope;
        let old_codemap = self.set_codemap(codemap);

        // Set up for the new function call
        let old_module_variables =
            mem::replace(&mut self.module_variables, module.map(|x| x.get()));
        self.is_module_scope = false;
        self.local_variables.push(locals);

        // Run the computation
        let res = within(self);

        // Restore them all back
        self.set_codemap(old_codemap);
        self.module_variables = old_module_variables;
        self.local_variables.pop();
        self.is_module_scope = old_is_module_scope;
        res
    }

    pub(crate) fn walk(&mut self, walker: &Walker<'v>) {
        let mut roots = self.module_env.slots().get_slots_mut();
        for x in roots.iter_mut() {
            walker.walk(x);
        }
        for locals in self.local_variables.iter_mut() {
            locals.walk(walker);
        }
        self.call_stack.walk(walker);
    }

    /// The active heap where [`Value`]s are allocated.
    pub fn heap(&self) -> &'v Heap {
        self.heap
    }

    /// The frozen heap. It's possible to allocate [`FrozenValue`](crate::values::FrozenValue)s here,
    /// but often not a great idea, as they will remain allocated as long
    /// as the results of this execution are required.
    /// Suitable for use with [`add_reference`](FrozenHeap::add_reference)
    /// and [`OwnedFrozenValue::owned_frozen_value`](crate::values::OwnedFrozenValue::owned_frozen_value).
    pub fn frozen_heap(&self) -> &FrozenHeap {
        self.module_env.frozen_heap()
    }

    pub(crate) fn get_slot_module(&self, slot: usize) -> anyhow::Result<Value<'v>> {
        match &self.module_variables {
            None => self.module_env.slots().get_slot(slot),
            Some(e) => e.get_slot(slot).map(Value::new_frozen),
        }
        .ok_or_else(|| {
            let name = match &self.module_variables {
                None => self.module_env.names().get_slot(slot),
                Some(e) => e.get_slot_name(slot),
            }
            .unwrap_or_else(|| "<unknown>".to_owned());
            EnvironmentError::LocalVariableReferencedBeforeAssignment(name).into()
        })
    }

    pub(crate) fn get_slot_local(&self, slot: usize, name: &str) -> anyhow::Result<Value<'v>> {
        self.local_variables.top().get_slot(slot).ok_or_else(|| {
            EnvironmentError::LocalVariableReferencedBeforeAssignment(name.to_owned()).into()
        })
    }

    pub(crate) fn clone_slot_reference(&self, slot: usize, heap: &'v Heap) -> ValueRef<'v> {
        self.local_variables.top().clone_slot_reference(slot, heap)
    }

    /// Set a variable in the module. Raises an error if called from a frozen module
    /// or not from the top-level.
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
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        if self.is_module_scope {
            value.export_as(name, heap);
            self.module_env.set(name, value);
            Ok(())
        } else {
            Err(EnvironmentError::CannotSetVariable(name.to_owned()).into())
        }
    }

    pub(crate) fn set_slot_module(&mut self, slot: usize, value: Value<'v>) {
        assert!(self.is_module_scope);
        self.module_env.slots().set_slot(slot, value);
    }

    pub(crate) fn set_slot_local(&mut self, slot: usize, value: Value<'v>) {
        self.local_variables.top().set_slot(slot, value)
    }

    pub(crate) fn assert_module_env(&self) -> &'v Module {
        if self.is_module_scope {
            self.module_env
        } else {
            panic!("this function is meant to be called only on module level")
        }
    }
}
