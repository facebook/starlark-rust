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

use crate as starlark;
use crate::{
    codemap::Span,
    eval::{Arguments, Evaluator, ParametersParser, ParametersSpec},
    values::{
        AllocFrozenValue, AllocValue, ComplexValue, Freezer, FrozenHeap, FrozenValue, Heap,
        SimpleValue, StarlarkValue, Trace, Value, ValueLike,
    },
};
use derivative::Derivative;
use gazebo::{any::AnyLifetime, coerce::Coerce};
use std::{cell::Cell, mem::MaybeUninit};

pub const FUNCTION_TYPE: &str = "function";

/// A native function that can be evaluated.
pub trait NativeFunc:
    for<'v> Fn(&mut Evaluator<'v, '_>, Arguments<'v, '_>) -> anyhow::Result<Value<'v>>
    + Send
    + Sync
    + 'static
{
}

impl<T> NativeFunc for T where
    T: for<'v> Fn(&mut Evaluator<'v, '_>, Arguments<'v, '_>) -> anyhow::Result<Value<'v>>
        + Send
        + Sync
        + 'static
{
}

/// A native function that can be evaluated.
pub trait NativeAttr:
    for<'v> Fn(Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>> + Send + Sync + 'static
{
}

impl<T> NativeAttr for T where
    T: for<'v> Fn(Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>>
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
    name: String,
    typ: Option<FrozenValue>,
}

impl AllocFrozenValue for NativeFunction {
    fn alloc_frozen_value(self, heap: &FrozenHeap) -> FrozenValue {
        heap.alloc_simple(self)
    }
}

impl NativeFunction {
    /// Create a new [`NativeFunction`] from the Rust function which works directly on the parameters.
    /// The called function is responsible for validating the parameters are correct.
    pub fn new_direct<F>(function: F, name: String) -> Self
    where
        // If I switch this to the trait alias then it fails to resolve the usages
        F: for<'v> Fn(&mut Evaluator<'v, '_>, Arguments<'v, '_>) -> anyhow::Result<Value<'v>>
            + Send
            + Sync
            + 'static,
    {
        NativeFunction {
            function: box function,
            name,
            typ: None,
        }
    }

    /// Create a new [`NativeFunction`] from the Rust function, plus the parameter specification.
    pub fn new<F>(function: F, name: String, parameters: ParametersSpec<FrozenValue>) -> Self
    where
        F: for<'v> Fn(
                &mut Evaluator<'v, '_>,
                Option<Value<'v>>,
                ParametersParser<'v, '_>,
            ) -> anyhow::Result<Value<'v>>
            + Send
            + Sync
            + 'static,
    {
        NativeFunction {
            function: box move |eval, params| {
                eval.alloca_uninit(parameters.len(), |slots, eval| {
                    // Fill in all the slots, because ValueRef lacks a Clone or similar
                    for slot in slots.iter_mut() {
                        slot.write(Cell::new(None));
                    }
                    let slots = unsafe { MaybeUninit::slice_assume_init_ref(slots) };

                    let this = params.this;
                    parameters.collect_inline(params, slots, eval.heap())?;
                    let parser = ParametersParser::new(slots);
                    function(eval, this, parser)
                })
            },
            name,
            typ: None,
        }
    }

    /// A `.type` value, if one exists. Specified using `#[starlark_type("the_type")]`.
    pub fn set_type(&mut self, typ: FrozenValue) {
        self.typ = Some(typ)
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
        s.push_str(&self.name)
    }

    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        eval.ann("invoke_native", |eval| {
            eval.with_call_stack(me, location, |eval| (self.function)(eval, args))
        })
    }

    fn extra_memory(&self) -> usize {
        self.name.capacity()
    }

    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> Option<Value<'v>> {
        if let Some(s) = &self.typ {
            if attribute == "type" {
                return Some(s.to_value());
            }
        }
        None
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
#[derive(Derivative)]
#[derivative(Debug)]
pub struct NativeAttribute {
    #[derivative(Debug = "ignore")]
    pub(crate) function: Box<dyn NativeAttr>,
}

starlark_simple_value!(NativeAttribute);

impl NativeAttribute {
    /// Create a new [`NativeFunction`] from the Rust function, plus the parameter specification.
    pub fn new<F>(function: F) -> Self
    where
        // If I switch this to the trait alias then it fails to resolve the usages
        F: for<'v> Fn(Value<'v>, &mut Evaluator<'v, '_>) -> anyhow::Result<Value<'v>>
            + Send
            + Sync
            + 'static,
    {
        NativeAttribute {
            function: box function,
        }
    }

    pub(crate) fn call<'v>(
        &self,
        value: Value<'v>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        (self.function)(value, eval)
    }
}

impl<'v> StarlarkValue<'v> for NativeAttribute {
    starlark_type!("attribute");

    fn invoke(
        &self,
        _me: Value<'v>,
        location: Option<Span>,
        args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        // If someone tries to invoke us with a this, first unwind the call, then continue onwards
        let me = self.call(args.this.unwrap(), eval)?;
        me.invoke(location, args, eval)
    }
}

/// A wrapper for a method with a self object already bound.
#[derive(Clone, Debug, Trace, Coerce)]
#[repr(C)]
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
    type Frozen = FrozenBoundMethod;
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        Ok(BoundMethodGen {
            method: self.method.freeze(freezer)?,
            this: self.this.freeze(freezer)?,
        })
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
        mut args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        args.this = Some(self.this.to_value());
        self.method.invoke(location, args, eval)
    }
}
