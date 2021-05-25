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

//! Function types, including native functions and `object.member` functions.

use crate::{
    codemap::Span,
    eval::{
        DefInvoker, DefInvokerFrozen, Evaluator, ParametersCollect, ParametersParser,
        ParametersSpec,
    },
    values::{
        AllocFrozenValue, AllocValue, ComplexValue, ConstFrozenValue, Freezer, FrozenHeap,
        FrozenValue, Hashed, Heap, SimpleValue, StarlarkValue, Value, ValueError, ValueLike,
        ValueRef, Walker,
    },
};
use derivative::Derivative;
use gazebo::{any::AnyLifetime, cell::ARef};

pub const FUNCTION_TYPE: &str = "function";

/// Function that can be invoked. Accumulates arguments before being called.
pub struct FunctionInvoker<'v> {
    pub(crate) collect: ParametersCollect<'v>,
    pub(crate) invoke: FunctionInvokerInner<'v>,
}

// Wrap to avoid exposing the enum alterantives
pub(crate) enum FunctionInvokerInner<'v> {
    Native(NativeFunctionInvoker<'v>),
    Def(DefInvoker<'v>),
    DefFrozen(DefInvokerFrozen<'v>),
}

impl<'v> FunctionInvoker<'v> {
    /// Actually invoke the underlying function, giving call-stack information.
    /// If provided, the `location` must use the currently active [`CodeMap`](crate::codemap::CodeMap)
    /// from the [`Evaluator`].
    pub fn invoke(
        self,
        function: Value<'v>,
        location: Option<Span>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let loc = location.map(|x| eval.file_span(x));
        let slots = self.collect.done(eval)?;
        let invoke = self.invoke;
        eval.with_call_stack(function, loc, |eval| match invoke {
            FunctionInvokerInner::Native(inv) => inv.invoke(slots, eval),
            FunctionInvokerInner::Def(inv) => inv.invoke(slots, eval),
            FunctionInvokerInner::DefFrozen(inv) => inv.invoke(slots, eval),
        })
    }

    /// Add a positional argument.
    pub fn push_pos(&mut self, v: Value<'v>, eval: &mut Evaluator<'v, '_>) {
        self.collect.push_pos(v, eval)
    }

    /// Add a `*args` argument.
    pub fn push_args(&mut self, v: Value<'v>, eval: &mut Evaluator<'v, '_>) {
        self.collect.push_args(v, eval)
    }

    /// Add a named argument.
    pub fn push_named(
        &mut self,
        name: &str,
        name_value: Hashed<Value<'v>>,
        v: Value<'v>,
        eval: &mut Evaluator<'v, '_>,
    ) {
        self.collect.push_named(name, name_value, v, eval)
    }

    /// Add a `**kargs` argument.
    pub fn push_kwargs(&mut self, v: Value<'v>, eval: &mut Evaluator<'v, '_>) {
        self.collect.push_kwargs(v, eval)
    }
}

/// A native function that can be evaluated.
pub trait NativeFunc:
    for<'v> Fn(&mut Evaluator<'v, '_>, ParametersParser<'v, '_>) -> anyhow::Result<Value<'v>>
    + Send
    + Sync
    + 'static
{
}

impl<T> NativeFunc for T where
    T: for<'v> Fn(&mut Evaluator<'v, '_>, ParametersParser<'v, '_>) -> anyhow::Result<Value<'v>>
        + Send
        + Sync
        + 'static
{
}

/// A function that can be evaluated which can also collect parameters
pub(crate) struct NativeFunctionInvoker<'a>(ARef<'a, dyn NativeFunc>);

impl<'a> NativeFunctionInvoker<'a> {
    pub fn new<'v, F: NativeFunc>(
        func: ARef<'v, NativeFunction<F>>,
        eval: &mut Evaluator<'v, '_>,
    ) -> FunctionInvoker<'v> {
        // Used to help guide the type checker
        fn convert(x: &impl NativeFunc) -> &(dyn NativeFunc) {
            x
        }

        let (function, parameters) =
            ARef::map_split(func, |x| (convert(&x.function), x.parameters.promote()));
        FunctionInvoker {
            collect: ParametersSpec::collect(parameters, 0, eval),
            invoke: FunctionInvokerInner::Native(NativeFunctionInvoker(function)),
        }
    }

    pub fn invoke<'v>(
        self,
        slots: Vec<ValueRef<'v>>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let parser = ParametersParser::new(&slots);
        (*self.0)(eval, parser)
    }
}

/// Starlark representation of native (Rust) functions.
///
/// Almost always created with [`#[starlark_module]`](macro@starlark_module).
#[derive(Derivative)]
#[derivative(Debug)]
pub struct NativeFunction<F: NativeFunc> {
    /// Pointer to a native function.
    /// Note it is a function pointer, not `Box<Fn(...)>`
    /// to avoid generic instantiation and allocation for each native function.
    #[derivative(Debug = "ignore")]
    function: F,
    parameters: ParametersSpec<FrozenValue>,
    typ: Option<FrozenValue>,
}

unsafe impl<'a, F: NativeFunc> AnyLifetime<'a> for NativeFunction<F> {
    any_lifetime_body!(Self);
}

impl<'v, F: NativeFunc> AllocFrozenValue for NativeFunction<F> {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(self)
    }
}

// If I switch this to the trait alias then it fails to resolve the usages
impl<
    F: for<'v> Fn(&mut Evaluator<'v, '_>, ParametersParser<'v, '_>) -> anyhow::Result<Value<'v>>
        + Send
        + Sync
        + 'static,
> NativeFunction<F>
{
    /// Create a new [`NativeFunction`] from the Rust function, plus the parameter specification.
    pub fn new(function: F, parameters: ParametersSpec<FrozenValue>) -> Self {
        NativeFunction {
            function,
            parameters,
            typ: None,
        }
    }

    /// A `.type` value, if one exists. Specified using `#[starlark_type("the_type")]`.
    pub fn set_type(&mut self, typ: &'static ConstFrozenValue) {
        self.typ = Some(typ.unpack())
    }
}

impl<F: NativeFunc> SimpleValue for NativeFunction<F> {}

impl<'v, F: NativeFunc> AllocValue<'v> for NativeFunction<F> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_simple(self)
    }
}

/// Define the function type
impl<'v, F: NativeFunc> StarlarkValue<'v> for NativeFunction<F> {
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, s: &mut String) {
        self.parameters.collect_repr(s)
    }

    fn new_invoker(
        &self,
        me: Value<'v>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<FunctionInvoker<'v>> {
        Ok(NativeFunctionInvoker::new(
            ARef::map(me.get_aref(), |x| {
                x.as_dyn_any().downcast_ref::<Self>().unwrap()
            }),
            eval,
        ))
    }

    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        if let Some(s) = &self.typ {
            if attribute == "type" {
                return Ok(s.to_value());
            }
        }
        ValueError::unsupported(self, &format!(".{}", attribute))
    }

    fn dir_attr(&self) -> Vec<String> {
        if self.typ.is_some() {
            vec!["type".to_owned()]
        } else {
            Vec::new()
        }
    }
}

/// Used by the `#[attribute]` tag of [`#[starlark_module]`](macro@starlark_module)
/// to define a function that pretends to be an attribute.
#[derive(Debug)]
pub struct NativeAttribute(FrozenValue); // Must be a NativeFunction

starlark_simple_value!(NativeAttribute);

impl NativeAttribute {
    /// Argument _must_ be a [`NativeFunction`] which takes one argument.
    pub fn new(x: FrozenValue) -> Self {
        NativeAttribute(x)
    }

    pub(crate) fn call<'v>(
        &self,
        value: Value<'v>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let function = self.0.to_value();
        let mut invoker = self.0.get_aref().new_invoker(function, eval)?;
        invoker.push_pos(value, eval);
        invoker.invoke(function, None, eval)
    }
}

impl<'v> StarlarkValue<'v> for NativeAttribute {
    starlark_type!("attribute");
}

/// A wrapper for a method with a self object already bound.
#[derive(Clone, Debug)]
pub struct WrappedMethodGen<V> {
    pub(crate) method: V,
    pub(crate) self_obj: V,
}

starlark_complex_value!(pub WrappedMethod);

impl<'v> WrappedMethod<'v> {
    /// Create a new [`WrappedMethod`]. Given the expression `object.function`,
    /// the first argument would be `object`, and the second would be `getattr(object, "function")`.
    pub fn new(self_obj: Value<'v>, method: Value<'v>) -> Self {
        WrappedMethod { method, self_obj }
    }
}

impl<'v, V: ValueLike<'v>> WrappedMethodGen<V> {
    pub(crate) fn invoke(
        &self,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<FunctionInvoker<'v>> {
        let mut inv = self.method.new_invoker(eval)?;
        inv.push_pos(self.self_obj.to_value(), eval);
        Ok(inv)
    }
}

impl<'v> ComplexValue<'v> for WrappedMethod<'v> {
    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        box WrappedMethodGen {
            method: self.method.freeze(freezer),
            self_obj: self.self_obj.freeze(freezer),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        walker.walk(&mut self.method);
        walker.walk(&mut self.self_obj);
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for WrappedMethodGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, s: &mut String) {
        self.method.collect_repr(s);
    }

    fn new_invoker(
        &self,
        _me: Value<'v>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<FunctionInvoker<'v>> {
        self.invoke(eval)
    }
}
