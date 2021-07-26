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
    codemap::Span,
    environment::Globals,
    eval::{Evaluator, Parameters},
    values::{
        layout::arena2::Reservation, ComplexValue, ConstFrozenValue, Freezer, Heap, SimpleValue,
        StarlarkValue, Tracer, Value,
    },
};
use gazebo::{
    any::AnyLifetime,
    cast,
    coerce::{coerce, Coerce},
};
use std::{
    any::TypeId,
    cmp::Ordering,
    fmt::{self, Debug},
    mem,
};

/// Occurs in "private" AValue methods, so has to be public, but don't tell anyone
#[doc(hidden)]
pub struct HiddenReservation<'v>(pub(crate) Reservation<'v>);

/// A trait that covers [`StarlarkValue`].
/// If you need a real [`StarlarkValue`] see [`AsStarlarkValue`](crate::values::AsStarlarkValue).
pub trait AValue<'v>: StarlarkValue<'v> {
    #[doc(hidden)]
    // How much memory I take up on the heap.
    // Included to allow unsized types to live on the heap.
    fn memory_size(&self) -> usize;

    #[doc(hidden)]
    fn trace(&mut self, tracer: &Tracer<'v>);

    #[doc(hidden)]
    fn reserve_simple<'a>(&self, freezer: &'a Freezer) -> HiddenReservation<'a>;

    #[doc(hidden)]
    fn fill_simple(
        self: Box<Self>,
        reservation: HiddenReservation,
        freezer: &Freezer,
    ) -> anyhow::Result<()>;

    fn unpack_str(&self) -> Option<&str> {
        self.unpack_box_str().map(|x| &**x)
    }

    #[allow(clippy::borrowed_box)]
    fn unpack_box_str(&self) -> Option<&Box<str>>;
}

impl<'v> dyn AValue<'v> {
    /// Downcast a reference to type `T`, or return [`None`](None) if it is not the
    /// right type.
    // We'd love to reuse the type from as_dyn_any, but that doesn't seem to have the right vtable-ness
    pub fn downcast_ref<T: AnyLifetime<'v>>(&self) -> Option<&T> {
        if self.static_type_of() == T::static_type_id() {
            // SAFETY: just checked whether we are pointing to the correct type.
            unsafe { Some(&*(self as *const Self as *const T)) }
        } else {
            None
        }
    }
}

pub(crate) fn basic_ref<'v, T: StarlarkValue<'v>>(x: &T) -> &dyn AValue<'v> {
    // These are the same representation, so safe to convert
    let x: &Wrapper<Basic, T> = unsafe { cast::ptr(x) };
    x
}

pub(crate) fn simple(x: impl SimpleValue) -> impl AValue<'static> + Send + Sync {
    Wrapper(Simple, x)
}

pub(crate) fn complex<'v>(x: impl ComplexValue<'v>) -> impl AValue<'v> {
    Wrapper(Complex, x)
}

// A type that implements StarlarkValue but nothing else, so will never be stored
// in the heap (e.g. bool, None)
struct Basic;

// A type that implements SimpleValue.
struct Simple;

// A type that implements ComplexValue.
struct Complex;

// We want to define several types (Simple, Complex) that wrap a StarlarkValue,
// reimplement it, and do some things custom. The easiest way to avoid repeating
// the StarlarkValue trait each time is to make them all share a single wrapper,
// where Mode is one of Simple/Complex.
#[repr(C)]
struct Wrapper<Mode, T>(Mode, T);

// Safe because Simple/Complex are ZST
unsafe impl<T> Coerce<T> for Wrapper<Simple, T> {}
unsafe impl<T> Coerce<T> for Wrapper<Complex, T> {}

impl<'v, T: StarlarkValue<'v>> AValue<'v> for Wrapper<Basic, T> {
    fn memory_size(&self) -> usize {
        mem::size_of::<Self>()
    }

    fn trace(&mut self, _tracer: &Tracer<'v>) {
        unreachable!("Basic types don't appear in the heap")
    }

    fn reserve_simple<'a>(&self, _freezer: &'a Freezer) -> HiddenReservation<'a> {
        unreachable!("Basic types don't appear in the heap")
    }

    fn fill_simple(
        self: Box<Self>,
        _reservation: HiddenReservation,
        _freezer: &Freezer,
    ) -> anyhow::Result<()> {
        unreachable!("Basic types don't appear in the heap")
    }

    fn unpack_box_str(&self) -> Option<&Box<str>> {
        None
    }
}

impl<'v, T: SimpleValue> AValue<'v> for Wrapper<Simple, T>
where
    'v: 'static,
{
    fn memory_size(&self) -> usize {
        mem::size_of::<Self>()
    }

    fn trace(&mut self, _tracer: &Tracer<'v>) {
        // Nothing to do
    }

    fn reserve_simple<'a>(&self, freezer: &'a Freezer) -> HiddenReservation<'a> {
        HiddenReservation(freezer.reserve::<Self>())
    }

    fn fill_simple(
        self: Box<Self>,
        reservation: HiddenReservation,
        _freezer: &Freezer,
    ) -> anyhow::Result<()> {
        reservation.0.fill(*self);
        Ok(())
    }

    fn unpack_box_str(&self) -> Option<&Box<str>> {
        // Do this entirely statically for best performance
        if T::static_type_id() == TypeId::of::<Box<str>>() {
            unsafe { Some(cast::ptr(&self.0)) }
        } else {
            None
        }
    }
}

impl<'v, T: ComplexValue<'v>> AValue<'v> for Wrapper<Complex, T> {
    fn memory_size(&self) -> usize {
        mem::size_of::<Self>()
    }

    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.1.trace(tracer)
    }

    fn reserve_simple<'a>(&self, freezer: &'a Freezer) -> HiddenReservation<'a> {
        HiddenReservation(freezer.reserve::<Wrapper<Simple, T::Frozen>>())
    }

    fn fill_simple(
        self: Box<Self>,
        reservation: HiddenReservation,
        freezer: &Freezer,
    ) -> anyhow::Result<()> {
        let x: Box<T> = coerce(self);
        let res = x.freeze(freezer)?;
        reservation.0.fill(simple(res));
        Ok(())
    }

    fn unpack_box_str(&self) -> Option<&Box<str>> {
        None
    }
}

impl<Mode, T: Debug> Debug for Wrapper<Mode, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.1.fmt(f)
    }
}

// This is somewhat dubious. We can't define Wrapper<T> to be AnyLifetime, since these things
// don't compose properly. We do layout Wrapper such that it is really a T underneath,
// so we can pretend it really is just a T.
unsafe impl<'v, Mode: 'static, T: AnyLifetime<'v>> AnyLifetime<'v> for Wrapper<Mode, T> {
    fn static_type_id() -> TypeId
    where
        Self: Sized,
    {
        T::static_type_id()
    }

    fn static_type_of(&self) -> std::any::TypeId {
        Self::static_type_id()
    }
}

#[derive(Debug, AnyLifetime)]
pub(crate) struct BlackHole0;

#[derive(Debug, AnyLifetime)]
pub(crate) struct BlackHole(pub(crate) usize);

impl<'v> AValue<'v> for BlackHole0 {
    fn memory_size(&self) -> usize {
        0
    }
    fn trace(&mut self, _tracer: &Tracer<'v>) {
        unreachable!()
    }
    fn reserve_simple<'a>(&self, _freezer: &'a Freezer) -> HiddenReservation<'a> {
        unreachable!()
    }
    fn fill_simple(
        self: Box<Self>,
        _reservation: HiddenReservation,
        _freezer: &Freezer,
    ) -> anyhow::Result<()> {
        unreachable!()
    }
    fn unpack_box_str(&self) -> Option<&Box<str>> {
        unreachable!()
    }
}

impl<'v> AValue<'v> for BlackHole {
    fn memory_size(&self) -> usize {
        self.0
    }

    fn trace(&mut self, _tracer: &Tracer<'v>) {
        unreachable!()
    }
    fn reserve_simple<'a>(&self, _freezer: &'a Freezer) -> HiddenReservation<'a> {
        unreachable!()
    }
    fn fill_simple(
        self: Box<Self>,
        _reservation: HiddenReservation,
        _freezer: &Freezer,
    ) -> anyhow::Result<()> {
        unreachable!()
    }
    fn unpack_box_str(&self) -> Option<&Box<str>> {
        unreachable!()
    }
}

impl<'v> StarlarkValue<'v> for BlackHole0 {
    starlark_type!("BlackHole0");
}

impl<'v> StarlarkValue<'v> for BlackHole {
    starlark_type!("BlackHole");
}

impl<'v, Mode: 'static, T: StarlarkValue<'v>> StarlarkValue<'v> for Wrapper<Mode, T> {
    fn get_type(&self) -> &'static str {
        self.1.get_type()
    }
    fn get_type_value(&self) -> &'static ConstFrozenValue {
        self.1.get_type_value()
    }
    fn matches_type(&self, ty: &str) -> bool {
        self.1.matches_type(ty)
    }
    fn get_methods(&self) -> Option<&'static Globals> {
        self.1.get_methods()
    }
    fn collect_repr(&self, collector: &mut String) {
        self.1.collect_repr(collector)
    }
    fn to_json(&self) -> anyhow::Result<String> {
        self.1.to_json()
    }
    fn to_bool(&self) -> bool {
        self.1.to_bool()
    }
    fn to_int(&self) -> anyhow::Result<i32> {
        self.1.to_int()
    }
    fn get_hash(&self) -> anyhow::Result<u64> {
        self.1.get_hash()
    }
    fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
        self.1.equals(other)
    }
    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        self.1.compare(other)
    }
    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        self.1.invoke(me, location, params, eval)
    }
    fn at(&self, index: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.at(index, heap)
    }
    fn slice(
        &self,
        start: Option<Value<'v>>,
        stop: Option<Value<'v>>,
        stride: Option<Value<'v>>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        self.1.slice(start, stop, stride, heap)
    }
    fn iterate(
        &'v self,
        heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'v>> {
        self.1.iterate(heap)
    }
    fn length(&self) -> anyhow::Result<i32> {
        self.1.length()
    }
    fn get_attr(&self, attribute: &str, heap: &'v Heap) -> Option<Value<'v>> {
        self.1.get_attr(attribute, heap)
    }
    fn has_attr(&self, attribute: &str) -> bool {
        self.1.has_attr(attribute)
    }
    fn dir_attr(&self) -> Vec<String> {
        self.1.dir_attr()
    }
    fn is_in(&self, other: Value<'v>) -> anyhow::Result<bool> {
        self.1.is_in(other)
    }
    fn plus(&self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.plus(heap)
    }
    fn minus(&self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.minus(heap)
    }
    fn radd(&self, lhs: Value<'v>, heap: &'v Heap) -> Option<anyhow::Result<Value<'v>>> {
        self.1.radd(lhs, heap)
    }
    fn add(&self, rhs: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.add(rhs, heap)
    }
    fn sub(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.sub(other, heap)
    }
    fn mul(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.mul(other, heap)
    }
    fn percent(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.percent(other, heap)
    }
    fn floor_div(&self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        self.1.floor_div(other, heap)
    }
    fn bit_and(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.1.bit_and(other)
    }
    fn bit_or(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.1.bit_or(other)
    }
    fn bit_xor(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.1.bit_xor(other)
    }
    fn left_shift(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.1.left_shift(other)
    }
    fn right_shift(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        self.1.right_shift(other)
    }
    fn export_as(&self, variable_name: &str, eval: &mut Evaluator<'v, '_>) {
        self.1.export_as(variable_name, eval)
    }
    fn set_at(&self, index: Value<'v>, new_value: Value<'v>) -> anyhow::Result<()> {
        self.1.set_at(index, new_value)
    }
    fn set_attr(&self, attribute: &str, new_value: Value<'v>) -> anyhow::Result<()> {
        self.1.set_attr(attribute, new_value)
    }
}
