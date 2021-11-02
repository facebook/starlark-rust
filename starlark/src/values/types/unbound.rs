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

//! Handle special "unbound" globals: methods or attributes.

use crate::values::{
    function::{BoundMethodGen, NativeAttribute, NativeMethod},
    FrozenValue, FrozenValueTyped, Heap, Value, ValueLike,
};

/// A value or an unbound method or unbound attribute.
pub(crate) enum MaybeUnboundValue<V> {
    /// Fully bound value, `this` is not used for it.
    Bound(V),
    /// A method with `this` unbound.
    Method(FrozenValueTyped<'static, NativeMethod>),
    /// An attribute with `this` unbound.
    Attr(FrozenValueTyped<'static, NativeAttribute>),
}

impl<'v, V: ValueLike<'v>> MaybeUnboundValue<V> {
    /// Bind this object to given `this` value.
    pub(crate) fn bind(self, this: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        match self {
            MaybeUnboundValue::Bound(v) => Ok(v.to_value()),
            MaybeUnboundValue::Method(m) => {
                Ok(heap.alloc_complex(BoundMethodGen::new(this.to_value(), m)))
            }
            MaybeUnboundValue::Attr(a) => a.call(this, heap),
        }
    }
}

impl MaybeUnboundValue<FrozenValue> {
    /// Split into variants.
    #[allow(clippy::same_functions_in_if_condition)] // False positive
    pub(crate) fn new(value: FrozenValue) -> MaybeUnboundValue<FrozenValue> {
        if let Some(method) = FrozenValueTyped::new(value) {
            MaybeUnboundValue::Method(method)
        } else if let Some(attr) = FrozenValueTyped::new(value) {
            MaybeUnboundValue::Attr(attr)
        } else {
            MaybeUnboundValue::Bound(value)
        }
    }

    /// Convert to non-frozen version of this.
    pub(crate) fn to_maybe_unbound_value<'v>(self) -> MaybeUnboundValue<Value<'v>> {
        match self {
            MaybeUnboundValue::Bound(value) => MaybeUnboundValue::Bound(value.to_value()),
            MaybeUnboundValue::Method(method) => MaybeUnboundValue::Method(method),
            MaybeUnboundValue::Attr(attr) => MaybeUnboundValue::Attr(attr),
        }
    }
}
