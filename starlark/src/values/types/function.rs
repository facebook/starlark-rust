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
    eval::{Evaluator, Parameters, ParametersParser, ParametersSpec},
    values::{
        AllocFrozenValue, AllocValue, ComplexValue, ConstFrozenValue, Freezer, FrozenHeap,
        FrozenValue, Heap, SimpleValue, StarlarkValue, Value, ValueError, ValueLike, Walker,
    },
};
use derivative::Derivative;
use gazebo::any::AnyLifetime;

pub const FUNCTION_TYPE: &str = "function";

/// A native function that can be evaluated.
pub trait NativeFunc:
    for<'v> Fn(&mut Evaluator<'v, '_>, ParametersParser) -> anyhow::Result<Value<'v>>
    + Send
    + Sync
    + 'static
{
}

impl<T> NativeFunc for T where
    T: for<'v> Fn(&mut Evaluator<'v, '_>, ParametersParser) -> anyhow::Result<Value<'v>>
        + Send
        + Sync
        + 'static
{
}

/// Starlark representation of native (Rust) functions.
///
/// Almost always created with [`#[starlark_module]`](macro@starlark_module).
#[derive(Derivative, AnyLifetime)]
#[derivative(Debug)]
pub struct NativeFunction {
    #[derivative(Debug = "ignore")]
    function: Box<dyn NativeFunc>,
    parameters: ParametersSpec<FrozenValue>,
    typ: Option<FrozenValue>,
}

impl AllocFrozenValue for NativeFunction {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(self)
    }
}

impl NativeFunction {
    /// Create a new [`NativeFunction`] from the Rust function, plus the parameter specification.
    pub fn new<F>(function: F, parameters: ParametersSpec<FrozenValue>) -> Self
    where
        // If I switch this to the trait alias then it fails to resolve the usages
        F: for<'v> Fn(&mut Evaluator<'v, '_>, ParametersParser) -> anyhow::Result<Value<'v>>
            + Send
            + Sync
            + 'static,
    {
        NativeFunction {
            function: box function,
            parameters,
            typ: None,
        }
    }

    /// A `.type` value, if one exists. Specified using `#[starlark_type("the_type")]`.
    pub fn set_type(&mut self, typ: &'static ConstFrozenValue) {
        self.typ = Some(typ.unpack())
    }
}

impl SimpleValue for NativeFunction {}

impl<'v> AllocValue<'v> for NativeFunction {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_simple(self)
    }
}

/// Define the function type
impl<'v> StarlarkValue<'v> for NativeFunction {
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, s: &mut String) {
        self.parameters.collect_repr(s)
    }

    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let mut collect = ParametersSpec::collect(self.parameters.promote(), 0, eval);
        collect.push_params(params, eval);
        let slots = collect.done(eval)?;
        eval.with_call_stack(me, location, |eval| {
            let parser = ParametersParser::new(slots);
            let res = (self.function)(eval, parser);
            eval.local_variables.release_after(slots);
            res
        })
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
        function.invoke_pos(None, &[value], eval)
    }
}

impl<'v> StarlarkValue<'v> for NativeAttribute {
    starlark_type!("attribute");
}

/// A wrapper for a method with a self object already bound.
#[derive(Clone, Debug)]
pub struct BoundMethodGen<V> {
    pub(crate) method: V,
    pub(crate) this: V,
}

starlark_complex_value!(pub BoundMethod);

impl<'v> BoundMethod<'v> {
    /// Create a new [`BoundMethod`]. Given the expression `object.function`,
    /// the first argument would be `object`, and the second would be `getattr(object, "function")`.
    pub fn new(this: Value<'v>, method: Value<'v>) -> Self {
        BoundMethod { method, this }
    }
}

impl<'v> ComplexValue<'v> for BoundMethod<'v> {
    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        box BoundMethodGen {
            method: self.method.freeze(freezer),
            this: self.this.freeze(freezer),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        walker.walk(&mut self.method);
        walker.walk(&mut self.this);
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for BoundMethodGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, s: &mut String) {
        self.method.collect_repr(s);
    }

    fn invoke(
        &self,
        _me: Value<'v>,
        location: Option<Span>,
        mut params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        params.this = Some(self.this.to_value());
        self.method.invoke(location, params, eval)
    }
}
