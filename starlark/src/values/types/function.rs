/*
 * Copyright 2018 The Starlark in Rust Authors.
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

//! Function as a TypedValue
use crate::{
    eval::{
        def::{DefInvoker, DefInvokerFrozen},
        Evaluator, Parameters, ParametersCollect,
    },
    stdlib::UnpackValue,
    values::{
        AllocFrozenValue, AllocValue, Freezer, FrozenHeap, FrozenValue, Hashed, Heap,
        ImmutableValue, MutableValue, TypedValue, Value, ValueError, ValueLike, Walker,
    },
};
use codemap::Span;
use derivative::Derivative;
use gazebo::{any::AnyLifetime, cell::ARef, prelude::*};
use std::slice::Iter;

pub const FUNCTION_VALUE_TYPE_NAME: &str = "function";

/// Invoke any type of function (native, def)
pub struct FunctionInvoker<'v, 'a>(pub(crate) FunctionInvokerInner<'v, 'a>);

// Wrap to avoid exposing the enum alterantives
pub(crate) enum FunctionInvokerInner<'v, 'a> {
    Native(NativeFunctionInvoker<'v, 'a>),
    Def(DefInvoker<'v, 'a>),
    DefFrozen(DefInvokerFrozen<'v, 'a>),
}

impl<'v, 'a> FunctionInvoker<'v, 'a> {
    pub fn invoke(
        self,
        function: Value<'v>,
        location: Option<Span>,
        context: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let loc = match location {
            None => None,
            Some(span) => Some((context.codemap.dupe(), span)),
        };
        context.with_call_stack(function, loc, |context| match self.0 {
            FunctionInvokerInner::Native(inv) => inv.invoke(context),
            FunctionInvokerInner::Def(inv) => inv.invoke(context),
            FunctionInvokerInner::DefFrozen(inv) => inv.invoke(context),
        })
    }

    pub fn push_pos(&mut self, v: Value<'v>) {
        match &mut self.0 {
            FunctionInvokerInner::Native(x) => x.collect().positional(v),
            FunctionInvokerInner::Def(x) => x.collect().positional(v),
            FunctionInvokerInner::DefFrozen(x) => x.collect().positional(v),
        }
    }

    pub fn push_args(&mut self, v: Value<'v>, heap: &'v Heap) {
        match &mut self.0 {
            FunctionInvokerInner::Native(x) => x.collect().args(v, heap),
            FunctionInvokerInner::Def(x) => x.collect().args(v, heap),
            FunctionInvokerInner::DefFrozen(x) => x.collect().args(v, heap),
        }
    }

    pub fn push_named(&mut self, name: &str, name_value: Hashed<Value<'v>>, v: Value<'v>) {
        match &mut self.0 {
            FunctionInvokerInner::Native(x) => x.collect().named(name, name_value, v),
            FunctionInvokerInner::Def(x) => x.collect().named(name, name_value, v),
            FunctionInvokerInner::DefFrozen(x) => x.collect().named(name, name_value, v),
        }
    }

    pub fn push_kwargs(&mut self, v: Value<'v>) {
        match &mut self.0 {
            FunctionInvokerInner::Native(x) => x.collect().kwargs(v),
            FunctionInvokerInner::Def(x) => x.collect().kwargs(v),
            FunctionInvokerInner::DefFrozen(x) => x.collect().kwargs(v),
        }
    }
}

/// Parse a series of parameters from a list of slots
pub struct ParameterParser<'v, 'a> {
    slots: Iter<'a, Option<Value<'v>>>,
}

impl<'v, 'a> ParameterParser<'v, 'a> {
    fn new(slots: &'a [Option<Value<'v>>]) -> Self {
        Self {
            slots: slots.iter(),
        }
    }

    // Utility for improving the error message with more information
    fn named_err<T>(name: &str, x: Option<T>) -> anyhow::Result<T> {
        x.ok_or_else(|| ValueError::IncorrectParameterTypeNamed(name.to_owned()).into())
    }

    // The next parameter, corresponding to Parameters.optional()
    pub fn next_opt<T: UnpackValue<'v>>(
        &mut self,
        name: &str,
        heap: &'v Heap,
    ) -> anyhow::Result<Option<T>> {
        // This unwrap is safe because we only call next one time per Parameters.count()
        // and slots starts out with that many entries.
        let v = self.slots.next().unwrap();
        match v {
            None => Ok(None),
            Some(v) => Ok(Some(Self::named_err(name, T::unpack_value(*v, heap))?)),
        }
    }

    // After ParametersCollect.done() all variables will be Some,
    // apart from those where we called Parameters.optional(),
    // and for those we chould call next_opt()
    pub fn next<T: UnpackValue<'v>>(&mut self, name: &str, heap: &'v Heap) -> anyhow::Result<T> {
        // This unwrap is safe because we only call next one time per Parameters.count()
        // and slots starts out with that many entries.
        let v = self.slots.next().unwrap();
        // This is definitely not unassigned because ParametersCollect.done checked
        // that.
        let v = v.as_ref().unwrap();
        Self::named_err(name, T::unpack_value(*v, heap))
    }
}

/// A native function that can be evaluated
pub trait NativeFunc:
    for<'v> Fn(&mut Evaluator<'v, '_>, ParameterParser<'v, '_>) -> anyhow::Result<Value<'v>>
    + Send
    + Sync
    + 'static
{
}

impl<T> NativeFunc for T where
    T: for<'v> Fn(&mut Evaluator<'v, '_>, ParameterParser<'v, '_>) -> anyhow::Result<Value<'v>>
        + Send
        + Sync
        + 'static
{
}

/// A function that can be evaluated which can also collect parameters
pub(crate) struct NativeFunctionInvoker<'v, 'a> {
    function: ARef<'a, dyn NativeFunc>,
    collect: ParametersCollect<'v, 'a, FrozenValue>,
}

impl<'v, 'a> NativeFunctionInvoker<'v, 'a> {
    pub fn new<F: NativeFunc>(func: ARef<'a, NativeFunction<F>>) -> Self {
        // Used to help guide the type checker
        fn convert(x: &impl NativeFunc) -> &(dyn NativeFunc) {
            x
        }

        let (function, parameters) =
            ARef::map_split(func, |x| (convert(&x.function), &x.parameters));
        Self {
            function,
            collect: Parameters::collect(parameters, 0),
        }
    }

    pub fn invoke(self, context: &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>> {
        let slots = self.collect.done(context.heap)?;
        let slots = slots.map(|x| x.get());
        let parser = ParameterParser::new(&slots);
        (*self.function)(context, parser)
    }

    fn collect(&mut self) -> &mut ParametersCollect<'v, 'a, FrozenValue> {
        &mut self.collect
    }
}

/// Function implementation for native (written in Rust) functions.
///
/// Public to be referenced in macros.
#[derive(Derivative)]
#[derivative(Debug)]
pub struct NativeFunction<F: NativeFunc> {
    /// Pointer to a native function.
    /// Note it is a function pointer, not `Box<Fn(...)>`
    /// to avoid generic instantiation and allocation for each native function.
    #[derivative(Debug = "ignore")]
    function: F,
    parameters: Parameters<FrozenValue>,
}

unsafe impl<'a, F: NativeFunc> AnyLifetime<'a> for NativeFunction<F> {
    any_lifetime_body!(Self);
}

impl<'v, F: NativeFunc> AllocFrozenValue<'v> for NativeFunction<F> {
    fn alloc_frozen_value(self, heap: &'v FrozenHeap) -> FrozenValue {
        heap.alloc_immutable(self)
    }
}

// If I switch this to the trait alias then it fails to resolve the usages
impl<
    F: for<'v> Fn(&mut Evaluator<'v, '_>, ParameterParser<'v, '_>) -> anyhow::Result<Value<'v>>
        + Send
        + Sync
        + 'static,
> NativeFunction<F>
{
    pub fn new(function: F, parameters: Parameters<FrozenValue>) -> Self {
        NativeFunction {
            function,
            parameters,
        }
    }
}

impl<'v, F: NativeFunc> ImmutableValue<'v> for NativeFunction<F> {}

impl<'v, F: NativeFunc> AllocValue<'v> for NativeFunction<F> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_immutable(self)
    }
}

/// Define the function type
impl<'v, F: NativeFunc> TypedValue<'v> for NativeFunction<F> {
    starlark_type!(FUNCTION_VALUE_TYPE_NAME);

    fn is_function(&self) -> bool {
        true
    }

    fn collect_repr(&self, s: &mut String) {
        self.parameters.collect_repr(s)
    }

    fn new_invoker<'a>(
        &self,
        me: Value<'v>,
        _heap: &'v Heap,
    ) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        Ok(FunctionInvoker(FunctionInvokerInner::Native(
            NativeFunctionInvoker::new(ARef::map(me.get_aref(), |x| {
                x.as_dyn_any().downcast_ref::<Self>().unwrap()
            })),
        )))
    }
}

#[derive(AnyLifetime, Debug)]
pub struct NativeAttribute(FrozenValue); // Must be a NativeFunction

impl NativeAttribute {
    // x must be a NativeFunction
    pub fn new(x: FrozenValue) -> Self {
        NativeAttribute(x)
    }

    pub(crate) fn call<'v>(
        &self,
        value: Value<'v>,
        context: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let function = self.0.to_value();
        let mut invoker = self.0.get_aref().new_invoker(function, context.heap)?;
        invoker.push_pos(value);
        invoker.invoke(function, None, context)
    }
}

impl<'v> TypedValue<'v> for NativeAttribute {
    starlark_type!("attribute");
}

impl<'v> ImmutableValue<'v> for NativeAttribute {}

impl<'v> AllocFrozenValue<'v> for NativeAttribute {
    fn alloc_frozen_value(self, heap: &'v FrozenHeap) -> FrozenValue {
        heap.alloc_immutable(self)
    }
}

impl<'v> AllocValue<'v> for NativeAttribute {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_immutable(self)
    }
}

// Wrapper for method that have been affected the self object
#[derive(Clone, Debug)]
pub struct WrappedMethodGen<V> {
    method: V,
    self_obj: V,
}

starlark_value!(pub WrappedMethod);

impl<'v> WrappedMethod<'v> {
    pub fn new(self_obj: Value<'v>, method: Value<'v>) -> Self {
        WrappedMethod { method, self_obj }
    }

    pub(crate) fn get_method(&self) -> Value<'v> {
        self.method
    }
}

impl<'v, V: ValueLike<'v>> WrappedMethodGen<V> {
    pub(crate) fn invoke<'a>(&self, heap: &'v Heap) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        let mut inv = self.method.new_invoker(heap)?;
        inv.push_pos(self.self_obj.to_value());
        Ok(inv)
    }
}

impl<'v> MutableValue<'v> for WrappedMethod<'v> {
    fn freeze<'fv>(self: Box<Self>, freezer: &'fv Freezer) -> Box<dyn ImmutableValue<'fv> + 'fv> {
        box WrappedMethodGen {
            method: self.method.freeze(freezer),
            self_obj: self.self_obj.freeze(freezer),
        }
    }

    fn walk(&mut self, walker: &Walker<'v>) {
        walker.walk(&mut self.method);
        walker.walk(&mut self.self_obj);
    }
}

impl<'v> ImmutableValue<'v> for FrozenWrappedMethod {}

impl<'v, V: ValueLike<'v>> TypedValue<'v> for WrappedMethodGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(FUNCTION_VALUE_TYPE_NAME);

    fn is_function(&self) -> bool {
        true
    }

    fn collect_repr(&self, s: &mut String) {
        self.method.collect_repr(s);
    }

    fn new_invoker<'a>(
        &self,
        _me: Value<'v>,
        heap: &'v Heap,
    ) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        self.invoke(heap)
    }
}
