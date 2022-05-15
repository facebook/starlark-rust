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

use std::{
    any::TypeId,
    cmp::Ordering,
    fmt,
    fmt::{Debug, Display},
    marker::PhantomData,
    mem, ptr,
    ptr::DynMetadata,
};

use gazebo::{any::AnyLifetime, dupe::Dupe};

use crate::{
    collections::{StarlarkHashValue, StarlarkHasher},
    environment::Methods,
    eval::{Arguments, Evaluator},
    values::{
        docs::DocItem,
        layout::{
            arena::{AValueHeader, AValueRepr},
            avalue::{AValue, BlackHole},
        },
        traits::{StarlarkValueVTable, StarlarkValueVTableGet},
        Freezer, FrozenStringValue, FrozenValue, Heap, StarlarkValue, Tracer, Value,
    },
};

struct GetDynMetadata<T>(PhantomData<T>);

/// Obtain vtables for supertraits of `StarlarkValue`.
///
/// These shoud be `const fn`, but currently rust does not allow it,
/// but allows associated consts.
impl<'v, T: Display + Debug + AnyLifetime<'v> + erased_serde::Serialize> GetDynMetadata<T> {
    const DISPLAY_DYN_METADATA: DynMetadata<dyn Display> = unsafe {
        ptr::metadata(transmute!(
            *const dyn Display,
            *const (dyn Display + 'static),
            ptr::null::<T>() as *const dyn Display
        ))
    };

    const DEBUG_DYN_METADATA: DynMetadata<dyn Debug> = unsafe {
        ptr::metadata(transmute!(
            *const dyn Debug,
            *const (dyn Debug + 'static),
            ptr::null::<T>() as *const dyn Debug
        ))
    };

    const ERASED_SERDE_SERIALIZE_DYN_METADATA: DynMetadata<dyn erased_serde::Serialize> = unsafe {
        ptr::metadata(transmute!(
            *const dyn erased_serde::Serialize,
            *const (dyn erased_serde::Serialize + 'static),
            ptr::null::<T>() as *const dyn erased_serde::Serialize
        ))
    };

    const ANY_LIFETIME_DYN_METADATA: DynMetadata<dyn AnyLifetime<'static>> = unsafe {
        ptr::metadata(transmute!(
            *const dyn AnyLifetime<'v>,
            *const (dyn AnyLifetime<'static> + 'static),
            ptr::null::<T>() as *const dyn AnyLifetime<'v>
        ))
    };
}

pub(crate) struct AValueVTable {
    // Common `AValue` fields.
    static_type_of_value: fn() -> TypeId,
    get_hash: fn(*const ()) -> anyhow::Result<StarlarkHashValue>,

    // `StarlarkValue`
    starlark_value: StarlarkValueVTable,

    // `Drop`
    drop_in_place: fn(*mut ()),

    // `AValue`
    is_str: bool,
    memory_size: fn(*const ()) -> usize,
    heap_freeze: fn(*mut (), &Freezer) -> anyhow::Result<FrozenValue>,
    heap_copy: for<'v> fn(*mut (), &Tracer<'v>) -> Value<'v>,

    // `StarlarkValue` supertraits
    // If we display often, we can optimize this by storing
    // a pointer to `Display::fmt` instead of a pointer to vtable.
    display: DynMetadata<dyn Display>,
    debug: DynMetadata<dyn Debug>,
    erased_serde_serialize: DynMetadata<dyn erased_serde::Serialize>,
    any_lifetime: DynMetadata<dyn AnyLifetime<'static>>,
}

impl AValueVTable {
    pub(crate) fn new_black_hole() -> &'static AValueVTable {
        &AValueVTable {
            drop_in_place: |_| {},

            is_str: false,
            memory_size: |p| unsafe { (*(p as *const BlackHole)).0 },
            static_type_of_value: || panic!("BlackHole"),

            heap_freeze: |_, _| panic!("BlackHole"),
            heap_copy: |_, _| panic!("BlackHole"),
            get_hash: |_| panic!("BlackHole"),

            display: GetDynMetadata::<BlackHole>::DISPLAY_DYN_METADATA,
            debug: GetDynMetadata::<BlackHole>::DEBUG_DYN_METADATA,
            erased_serde_serialize:
                GetDynMetadata::<BlackHole>::ERASED_SERDE_SERIALIZE_DYN_METADATA,
            any_lifetime: GetDynMetadata::<BlackHole>::ANY_LIFETIME_DYN_METADATA,
            starlark_value: StarlarkValueVTable::BLACK_HOLE,
        }
    }

    pub(crate) const fn new<'v, T: AValue<'v>>() -> &'static AValueVTable {
        &AValueVTable {
            drop_in_place: |p| unsafe {
                ptr::drop_in_place(p as *mut T);
            },
            is_str: T::IS_STR,
            memory_size: |p| unsafe {
                let p = p as *const T;
                T::memory_size_for_extra_len((*p).extra_len())
            },
            heap_freeze: |p, freezer| unsafe {
                let p = &mut *AValueRepr::from_payload_ptr_mut(p as *mut T);
                T::heap_freeze(p, transmute!(&Freezer, &Freezer, freezer))
            },
            heap_copy: |p, tracer| unsafe {
                let p = &mut *AValueRepr::from_payload_ptr_mut(p as *mut T);
                let value = T::heap_copy(p, transmute!(&Tracer, &Tracer, tracer));
                transmute!(Value, Value, value)
            },
            static_type_of_value: T::StarlarkValue::static_type_id,
            get_hash: |p| unsafe {
                let p = &*(p as *const T);
                T::get_hash(p)
            },
            display: GetDynMetadata::<T::StarlarkValue>::DISPLAY_DYN_METADATA,
            debug: GetDynMetadata::<T::StarlarkValue>::DEBUG_DYN_METADATA,
            erased_serde_serialize:
                GetDynMetadata::<T::StarlarkValue>::ERASED_SERDE_SERIALIZE_DYN_METADATA,
            any_lifetime: GetDynMetadata::<T::StarlarkValue>::ANY_LIFETIME_DYN_METADATA,
            starlark_value: StarlarkValueVTableGet::<'v, T::StarlarkValue>::VTABLE,
        }
    }

    pub(crate) fn drop_in_place(&self, value: *mut ()) {
        (self.drop_in_place)(value)
    }
}

#[derive(Copy, Clone, Dupe)]
#[repr(C)]
pub(crate) struct AValueDyn<'v> {
    pub(crate) value: &'v (),
    pub(crate) vtable: &'static AValueVTable,
}

impl<'v> AValueDyn<'v> {
    pub(crate) fn memory_size(self) -> usize {
        (self.vtable.memory_size)(self.value as *const ())
    }

    pub(crate) fn total_memory(self) -> usize {
        mem::size_of::<AValueHeader>()
            + self.memory_size()
            + (self.vtable.starlark_value.extra_memory)(self.value as *const ())
    }

    pub(crate) fn get_type(self) -> &'static str {
        (self.vtable.starlark_value.get_type)(self.value as *const ())
    }

    pub(crate) fn get_type_value(self) -> FrozenStringValue {
        (self.vtable.starlark_value.get_type_value_static)()
    }

    pub(crate) fn static_type_of_value(self) -> TypeId {
        (self.vtable.static_type_of_value)()
    }

    pub(crate) fn is_str(self) -> bool {
        self.vtable.is_str
    }

    pub(crate) unsafe fn heap_freeze(self, freezer: &Freezer) -> anyhow::Result<FrozenValue> {
        (self.vtable.heap_freeze)(self.value as *const _ as *mut (), freezer)
    }

    pub(crate) unsafe fn heap_copy(self, tracer: &Tracer<'v>) -> Value<'v> {
        (self.vtable.heap_copy)(self.value as *const _ as *mut (), tracer)
    }

    pub(crate) fn documentation(self) -> Option<DocItem> {
        (self.vtable.starlark_value.documentation)(self.value as *const ())
    }

    pub(crate) fn get_methods(self) -> Option<&'static Methods> {
        (self.vtable.starlark_value.get_methods)(self.value as *const ())
    }

    pub(crate) fn at(self, index: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.at)(self.value as *const (), index, heap)
    }

    pub(crate) fn is_in(self, collection: Value<'v>) -> anyhow::Result<bool> {
        (self.vtable.starlark_value.is_in)(self.value as *const (), collection)
    }

    pub(crate) fn slice(
        self,
        start: Option<Value<'v>>,
        stop: Option<Value<'v>>,
        step: Option<Value<'v>>,
        heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.slice)(self.value as *const (), start, stop, step, heap)
    }

    pub(crate) fn get_attr(self, name: &str, heap: &'v Heap) -> Option<Value<'v>> {
        (self.vtable.starlark_value.get_attr)(self.value as *const (), name, heap)
    }

    pub(crate) fn has_attr(self, name: &str) -> bool {
        (self.vtable.starlark_value.has_attr)(self.value as *const (), name)
    }

    pub(crate) fn dir_attr(self) -> Vec<String> {
        (self.vtable.starlark_value.dir_attr)(self.value as *const ())
    }

    pub(crate) fn bit_and(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.bit_and)(self.value as *const (), other, heap)
    }

    pub(crate) fn bit_or(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.bit_or)(self.value as *const (), other, heap)
    }

    pub(crate) fn bit_xor(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.bit_xor)(self.value as *const (), other, heap)
    }

    pub(crate) fn bit_not(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.bit_not)(self.value as *const (), heap)
    }

    pub(crate) fn to_int(self) -> anyhow::Result<i32> {
        (self.vtable.starlark_value.to_int)(self.value as *const ())
    }

    pub(crate) fn to_bool(self) -> bool {
        (self.vtable.starlark_value.to_bool)(self.value as *const ())
    }

    pub(crate) fn length(self) -> anyhow::Result<i32> {
        (self.vtable.starlark_value.length)(self.value as *const ())
    }

    pub(crate) fn iterate<'a>(
        self,
        heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'v>>
    where
        'v: 'a,
    {
        (self.vtable.starlark_value.iterate)(self.value as *const (), heap)
    }

    pub(crate) fn with_iterator(
        self,
        heap: &'v Heap,
        f: &mut dyn FnMut(&mut dyn Iterator<Item = Value<'v>>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        (self.vtable.starlark_value.with_iterator)(self.value as *const (), heap, f)
    }

    pub(crate) fn get_hash(self) -> anyhow::Result<StarlarkHashValue> {
        (self.vtable.get_hash)(self.value as *const ())
    }

    pub(crate) fn plus(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.plus)(self.value as *const (), heap)
    }

    pub(crate) fn minus(self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.minus)(self.value as *const (), heap)
    }

    pub(crate) fn add(self, other: Value<'v>, heap: &'v Heap) -> Option<anyhow::Result<Value<'v>>> {
        (self.vtable.starlark_value.add)(self.value as *const (), other, heap)
    }

    pub(crate) fn radd(
        self,
        other: Value<'v>,
        heap: &'v Heap,
    ) -> Option<anyhow::Result<Value<'v>>> {
        (self.vtable.starlark_value.radd)(self.value as *const (), other, heap)
    }

    pub(crate) fn sub(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.sub)(self.value as *const (), other, heap)
    }

    pub(crate) fn mul(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.mul)(self.value as *const (), other, heap)
    }

    pub(crate) fn div(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.div)(self.value as *const (), other, heap)
    }

    pub(crate) fn floor_div(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.floor_div)(self.value as *const (), other, heap)
    }

    pub(crate) fn percent(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.percent)(self.value as *const (), other, heap)
    }

    pub(crate) fn left_shift(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.left_shift)(self.value as *const (), other, heap)
    }

    pub(crate) fn right_shift(self, other: Value<'v>, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.right_shift)(self.value as *const (), other, heap)
    }

    pub(crate) fn collect_repr(self, collector: &mut String) {
        (self.vtable.starlark_value.collect_repr)(self.value as *const (), collector)
    }

    pub(crate) fn collect_repr_cycle(self, collector: &mut String) {
        (self.vtable.starlark_value.collect_repr_cycle)(self.value as *const (), collector)
    }

    pub(crate) fn downcast_ref<T: StarlarkValue<'v>>(self) -> Option<&'v T> {
        if self.static_type_of_value() == T::static_type_id() {
            // SAFETY: just checked whether we are pointing to the correct type.
            unsafe { Some(&*(self.value as *const () as *const T)) }
        } else {
            None
        }
    }

    pub(crate) fn equals(self, other: Value<'v>) -> anyhow::Result<bool> {
        (self.vtable.starlark_value.equals)(self.value as *const (), other)
    }

    pub(crate) fn compare(self, other: Value<'v>) -> anyhow::Result<Ordering> {
        (self.vtable.starlark_value.compare)(self.value as *const (), other)
    }

    pub(crate) fn invoke(
        self,
        me: Value<'v>,
        args: &Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.invoke)(self.value as *const (), me, args, eval)
    }

    pub(crate) fn invoke_method(
        self,
        me: Value<'v>,
        this: Value<'v>,
        args: &Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        (self.vtable.starlark_value.invoke_method)(self.value as *const (), me, this, args, eval)
    }

    pub(crate) fn name_for_call_stack(self, me: Value<'v>) -> String {
        (self.vtable.starlark_value.name_for_call_stack)(self.value as *const (), me)
    }

    pub(crate) fn export_as(self, variable_name: &str, eval: &mut Evaluator<'v, '_>) {
        (self.vtable.starlark_value.export_as)(self.value as *const (), variable_name, eval)
    }

    pub(crate) fn set_at(self, index: Value<'v>, new_value: Value<'v>) -> anyhow::Result<()> {
        (self.vtable.starlark_value.set_at)(self.value as *const (), index, new_value)
    }

    pub(crate) fn set_attr(self, attribute: &str, new_value: Value<'v>) -> anyhow::Result<()> {
        (self.vtable.starlark_value.set_attr)(self.value as *const (), attribute, new_value)
    }

    pub(crate) fn write_hash(self, hasher: &mut StarlarkHasher) -> anyhow::Result<()> {
        (self.vtable.starlark_value.write_hash)(self.value as *const (), hasher)
    }

    pub(crate) fn matches_type(self, t: &str) -> bool {
        (self.vtable.starlark_value.matches_type)(self.value as *const (), t)
    }

    pub(crate) fn as_display(self) -> &'v dyn Display {
        unsafe { &*ptr::from_raw_parts(self.value as *const (), self.vtable.display) }
    }

    pub(crate) fn as_debug(self) -> &'v dyn fmt::Debug {
        unsafe { &*ptr::from_raw_parts(self.value as *const (), self.vtable.debug) }
    }

    pub(crate) fn as_serialize(self) -> &'v dyn erased_serde::Serialize {
        unsafe {
            &*ptr::from_raw_parts(self.value as *const (), self.vtable.erased_serde_serialize)
        }
    }

    pub(crate) fn value_as_dyn_any(self) -> &'v dyn AnyLifetime<'v> {
        let any_lifetime = unsafe {
            transmute!(
                DynMetadata<dyn AnyLifetime<'static>>,
                DynMetadata::<dyn AnyLifetime<'v>>,
                self.vtable.any_lifetime
            )
        };
        unsafe { &*ptr::from_raw_parts(self.value as *const (), any_lifetime) }
    }
}
