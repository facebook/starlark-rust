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
    cell::{Cell, RefCell},
    cmp,
    collections::HashSet,
    fmt,
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
    intrinsics::copy_nonoverlapping,
    marker::PhantomData,
    mem::MaybeUninit,
    ops::Deref,
    ptr,
    sync::Arc,
    usize,
};

use either::Either;
use gazebo::{cast, prelude::*};

use crate::{
    collections::Hashed,
    eval::FrozenDef,
    values::{
        any::StarlarkAny,
        array::Array,
        constant_string,
        layout::{
            arena::{AValueHeader, AValueRepr, Arena, HeapSummary, Reservation},
            avalue::{
                array_avalue, complex, float_avalue, frozen_list_avalue, frozen_tuple_avalue,
                list_avalue, simple, starlark_str, tuple_avalue, AValue, VALUE_EMPTY_ARRAY,
                VALUE_EMPTY_FROZEN_LIST, VALUE_EMPTY_TUPLE,
            },
            value::{FrozenValue, Value},
        },
        string::hash_string_result,
        types::float::StarlarkFloat,
        AllocFrozenValue, ComplexValue, FrozenRef, FrozenValueTyped, SimpleValue, ValueTyped,
    },
};

/// A heap on which [`Value`]s can be allocated. The values will be annotated with the heap lifetime.
#[derive(Default)]
pub struct Heap {
    /// Peak memory seen when a garbage collection takes place (may be lower than currently allocated)
    peak_allocated: Cell<usize>,
    arena: RefCell<Arena>,
}

impl Debug for Heap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut x = f.debug_struct("Heap");
        x.field(
            "bytes",
            &self.arena.try_borrow().map(|x| x.allocated_bytes()),
        );
        x.finish()
    }
}

/// A heap on which [`FrozenValue`]s can be allocated.
/// Can be kept alive by a [`FrozenHeapRef`].
#[derive(Default)]
pub struct FrozenHeap {
    arena: Arena,                          // My memory
    refs: RefCell<HashSet<FrozenHeapRef>>, // Memory I depend on
}

/// `FrozenHeap` when it is no longer modified and can be share between threads.
/// Although, `arena` is not safe to share between threads, but at least `refs` is.
#[derive(Default)]
struct FrozenFrozenHeap {
    arena: Arena,
    refs: HashSet<FrozenHeapRef>,
}

impl Debug for FrozenHeap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut x = f.debug_struct("FrozenHeap");
        x.field("bytes", &self.arena.allocated_bytes());
        x.field("refs", &self.refs.try_borrow().map(|x| x.len()));
        x.finish()
    }
}

impl Debug for FrozenFrozenHeap {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut x = f.debug_struct("FrozenHeap");
        x.field("bytes", &self.arena.allocated_bytes());
        x.field("refs", &self.refs.len());
        x.finish()
    }
}

// Safe because we never mutate the Arena other than with &mut
unsafe impl Sync for FrozenHeapRef {}
unsafe impl Send for FrozenHeapRef {}

/// A reference to a [`FrozenHeap`] that keeps alive all values on the underlying heap.
/// Note that the [`Hash`] is consistent for a single [`FrozenHeapRef`], but non-deterministic
/// across executions and distinct but observably identical [`FrozenHeapRef`] values.
#[derive(Clone, Dupe, Debug)]
// The Eq/Hash are by pointer rather than value, since we produce unique values
// given an underlying FrozenHeap.
pub struct FrozenHeapRef(Arc<FrozenFrozenHeap>);

impl Hash for FrozenHeapRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let x: &FrozenFrozenHeap = Deref::deref(&self.0);
        ptr::hash(x, state);
    }
}

impl PartialEq<FrozenHeapRef> for FrozenHeapRef {
    fn eq(&self, other: &FrozenHeapRef) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for FrozenHeapRef {}

impl FrozenHeapRef {
    /// Number of bytes allocated on this heap, not including any memory
    /// represented by [`extra_memory`](crate::values::StarlarkValue::extra_memory).
    pub fn allocated_bytes(&self) -> usize {
        self.0.arena.allocated_bytes()
    }

    /// Number of bytes allocated by the heap but not filled.
    /// Note that these bytes will _never_ be filled as no further allocations can
    /// be made on this heap (it has been sealed).
    pub fn available_bytes(&self) -> usize {
        self.0.arena.available_bytes()
    }

    /// Obtain a summary of how much memory is currently allocated by this heap.
    /// Doesn't include the heaps it keeps alive by reference.
    pub fn allocated_summary(&self) -> HeapSummary {
        self.0.arena.allocated_summary()
    }
}

impl FrozenHeap {
    /// Create a new [`FrozenHeap`].
    pub fn new() -> Self {
        Self::default()
    }

    /// After all values have been allocated, convert the [`FrozenHeap`] into a
    /// [`FrozenHeapRef`] which can be [`clone`](Clone::clone)d, shared between threads,
    /// and ensures the underlying values allocated on the [`FrozenHeap`] remain valid.
    pub fn into_ref(self) -> FrozenHeapRef {
        let FrozenHeap { arena, refs } = self;
        FrozenHeapRef(Arc::new(FrozenFrozenHeap {
            arena,
            refs: refs.into_inner(),
        }))
    }

    /// Keep the argument [`FrozenHeapRef`] alive as long as this [`FrozenHeap`]
    /// is kept alive. Used if a [`FrozenValue`] in this heap points at values in another
    /// [`FrozenHeap`].
    pub fn add_reference(&self, heap: &FrozenHeapRef) {
        self.refs.borrow_mut().get_or_insert_owned(heap);
    }

    fn alloc_raw(&self, x: impl AValue<'static, ExtraElem = ()>) -> FrozenValue {
        let v: &AValueRepr<_> = self.arena.alloc(x);
        unsafe { FrozenValue::new_repr(cast::ptr_lifetime(v)) }
    }

    /// Allocate a string on this heap. Be careful about the warnings
    /// around [`FrozenValue`].
    pub(crate) fn alloc_str(&self, x: &str) -> FrozenValue {
        if let Some(x) = constant_string(x) {
            x.unpack()
        } else {
            let (v, extra) = self.arena.alloc_extra_non_drop(starlark_str(x.len()));
            MaybeUninit::write_slice(extra, x.as_bytes());
            FrozenValue::new_repr(unsafe { cast::ptr_lifetime(&*v) })
        }
    }

    /// Allocate a string on this heap and hash it. Be careful about the warnings
    /// around [`FrozenValue`].
    pub fn alloc_str_hashed(&self, x: &str) -> Hashed<FrozenValue> {
        let h = hash_string_result(x);
        Hashed::new_unchecked(h, self.alloc_str(x))
    }

    pub fn alloc_tuple<'v>(&'v self, elems: &[FrozenValue]) -> FrozenValue {
        if elems.is_empty() {
            return FrozenValue::new_repr(&VALUE_EMPTY_TUPLE);
        }

        unsafe {
            let (avalue, extra) = self
                .arena
                .alloc_extra_non_drop::<_>(frozen_tuple_avalue(elems.len()));
            MaybeUninit::write_slice(extra, elems);
            FrozenValue::new_repr(&*avalue)
        }
    }

    pub fn alloc_list(&self, elems: &[FrozenValue]) -> FrozenValue {
        if elems.is_empty() {
            return FrozenValue::new_repr(&VALUE_EMPTY_FROZEN_LIST);
        }

        unsafe {
            let (avalue, elem_places) = self
                .arena
                .alloc_extra_non_drop(frozen_list_avalue(elems.len()));
            MaybeUninit::write_slice(elem_places, elems);
            FrozenValue::new_repr(&*avalue)
        }
    }

    pub(crate) fn alloc_float(&self, f: StarlarkFloat) -> FrozenValue {
        self.alloc_raw(float_avalue(f))
    }

    /// Allocate a [`SimpleValue`] on this heap. Be careful about the warnings
    /// around [`FrozenValue`].
    pub fn alloc_simple<T: SimpleValue>(&self, val: T) -> FrozenValue {
        self.alloc_raw(simple(val))
    }

    /// Allocate a [`SimpleValue`] and return `FrozenRef` to it.
    pub(crate) fn alloc_simple_frozen_ref<T: SimpleValue>(&self, value: T) -> FrozenRef<T> {
        let value = self.alloc_simple(value);
        // Here we could avoid dynamic cast, but this code is not executed frequently.
        value.downcast_frozen_ref().unwrap()
    }

    /// Allocate any value in the frozen heap.
    pub(crate) fn alloc_any<T: Debug + Display + Send + Sync>(&self, value: T) -> FrozenRef<T> {
        let value = self.alloc_simple_frozen_ref(StarlarkAny::new(value));
        value.map(|r| &r.0)
    }

    /// Number of bytes allocated on this heap, not including any memory
    /// represented by [`extra_memory`](crate::values::StarlarkValue::extra_memory).
    pub fn allocated_bytes(&self) -> usize {
        self.arena.allocated_bytes()
    }

    /// Number of bytes allocated by the heap but not yet filled.
    pub fn available_bytes(&self) -> usize {
        self.arena.available_bytes()
    }

    /// Obtain a summary of how much memory is currently allocated by this heap.
    pub fn allocated_summary(&self) -> HeapSummary {
        self.arena.allocated_summary()
    }
}

/// Used to `freeze` values by [`Freeze::freeze`](crate::values::Freeze::freeze).
// A freezer is a pair of the FrozenHeap and a "magic" value,
// which we happen to use for the slots (see `FrozenSlotsRef`)
// but could be used for anything.
pub struct Freezer {
    /// Freezing into this heap.
    pub(crate) heap: FrozenHeap,
    /// Defs frozen by this freezer.
    pub(crate) frozen_defs: RefCell<Vec<FrozenRef<FrozenDef>>>,
}

impl Freezer {
    pub(crate) fn new(heap: FrozenHeap) -> Self {
        Freezer {
            heap,
            frozen_defs: RefCell::new(Vec::new()),
        }
    }

    pub(crate) fn into_ref(self) -> FrozenHeapRef {
        self.heap.into_ref()
    }

    /// Allocate a new value while freezing. Usually not a great idea.
    pub fn alloc<'v, T: AllocFrozenValue>(&'v self, val: T) -> FrozenValue {
        val.alloc_frozen_value(&self.heap)
    }

    pub(crate) fn reserve<'v, 'v2: 'v, T: AValue<'v2, ExtraElem = ()>>(
        &'v self,
    ) -> (FrozenValue, Reservation<'v, 'v2, T>) {
        let (fv, r, extra) = self.reserve_with_extra::<T>(0);
        debug_assert!(extra.is_empty());
        (fv, r)
    }

    pub(crate) fn reserve_with_extra<'v, 'v2: 'v, T: AValue<'v2>>(
        &'v self,
        extra_len: usize,
    ) -> (
        FrozenValue,
        Reservation<'v, 'v2, T>,
        &'v mut [MaybeUninit<T::ExtraElem>],
    ) {
        let (r, extra) = self.heap.arena.reserve_with_extra::<T>(extra_len);
        let fv = FrozenValue::new_ptr(unsafe { cast::ptr_lifetime(r.ptr()) }, false);
        (fv, r, extra)
    }

    /// Freeze a nested value while freezing yourself.
    pub fn freeze(&self, value: Value) -> anyhow::Result<FrozenValue> {
        // Case 1: We have our value encoded in our pointer
        if let Some(x) = value.unpack_frozen() {
            return Ok(x);
        }

        // Case 2: We have already been replaced with a forwarding, or need to freeze
        let value = value.0.unpack_ptr().unwrap();
        match value.unpack_overwrite() {
            Either::Left(x) => Ok(FrozenValue::new_ptr_usize_with_str_tag(x)),
            Either::Right(v) => unsafe {
                v.heap_freeze(value as *const AValueHeader as *mut AValueHeader, self)
            },
        }
    }
}

impl Heap {
    /// Create a new [`Heap`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of bytes allocated on this heap, not including any memory
    /// represented by [`extra_memory`](crate::values::StarlarkValue::extra_memory).
    pub fn allocated_bytes(&self) -> usize {
        self.arena.borrow().allocated_bytes()
    }

    /// Peak memory allocated to this heap, even if the value is now lower
    /// as a result of a subsequent garbage collection.
    pub fn peak_allocated_bytes(&self) -> usize {
        cmp::max(self.allocated_bytes(), self.peak_allocated.get())
    }

    /// Number of bytes allocated by the heap but not yet filled.
    pub fn available_bytes(&self) -> usize {
        self.arena.borrow().available_bytes()
    }

    fn alloc_raw<'v, 'v2: 'v2>(&'v self, x: impl AValue<'v2, ExtraElem = ()>) -> Value<'v> {
        let arena_ref = self.arena.borrow_mut();
        let arena = &*arena_ref;
        let v: &AValueRepr<_> = arena.alloc(x);

        // We have an arena inside a RefCell which stores ValueMem<'v>
        // However, we promise not to clear the RefCell other than for GC
        // so we can make the `arena` available longer
        unsafe {
            let value = Value::new_repr(cast::ptr_lifetime(v));
            transmute!(Value, Value, value)
        }
    }

    fn alloc_raw_typed<'v, A: AValue<'v, ExtraElem = ()>>(
        &'v self,
        x: A,
    ) -> ValueTyped<'v, A::StarlarkValue> {
        unsafe { ValueTyped::new_unchecked(self.alloc_raw(x)) }
    }

    pub(crate) fn alloc_str_init<'v>(
        &'v self,
        len: usize,
        init: impl FnOnce(*mut u8),
    ) -> Value<'v> {
        let arena_ref = self.arena.borrow_mut();
        let arena = &*arena_ref;
        let (v, extra) = arena.alloc_extra_non_drop::<_>(starlark_str(len));
        init(extra.as_mut_ptr() as *mut u8);

        // We have an arena inside a RefCell which stores ValueMem<'v>
        // However, we promise not to clear the RefCell other than for GC
        // so we can make the `arena` available longer
        unsafe { transmute!(Value, Value, Value::new_repr(&*v)) }
    }

    /// Allocate a string on the heap.
    pub fn alloc_str<'v>(&'v self, x: &str) -> Value<'v> {
        if let Some(x) = constant_string(x) {
            x.unpack().to_value()
        } else {
            self.alloc_str_init(x.len(), |dest| unsafe {
                copy_nonoverlapping(x.as_ptr(), dest, x.len())
            })
        }
    }

    /// Allocate a string on this heap and hash it.
    pub fn alloc_str_hashed<'v>(&'v self, x: &str) -> Hashed<Value<'v>> {
        let h = hash_string_result(x);
        Hashed::new_unchecked(h, self.alloc_str(x))
    }

    pub(crate) fn alloc_str_concat<'v>(&'v self, x: &str, y: &str) -> Value<'v> {
        if x.is_empty() {
            self.alloc_str(y)
        } else if y.is_empty() {
            self.alloc_str(x)
        } else {
            self.alloc_str_init(x.len() + y.len(), |dest| unsafe {
                copy_nonoverlapping(x.as_ptr(), dest, x.len());
                copy_nonoverlapping(y.as_ptr(), dest.add(x.len()), y.len())
            })
        }
    }

    pub(crate) fn alloc_str_concat3<'v>(&'v self, x: &str, y: &str, z: &str) -> Value<'v> {
        if x.is_empty() {
            self.alloc_str_concat(y, z)
        } else if y.is_empty() {
            self.alloc_str_concat(x, z)
        } else if z.is_empty() {
            self.alloc_str_concat(x, y)
        } else {
            self.alloc_str_init(x.len() + y.len() + z.len(), |dest| unsafe {
                copy_nonoverlapping(x.as_ptr(), dest, x.len());
                let dest = dest.add(x.len());
                copy_nonoverlapping(y.as_ptr(), dest, y.len());
                let dest = dest.add(y.len());
                copy_nonoverlapping(z.as_ptr(), dest, z.len());
            })
        }
    }

    pub fn alloc_tuple<'v>(&'v self, elems: &[Value<'v>]) -> Value<'v> {
        if elems.is_empty() {
            return FrozenValue::new_repr(&VALUE_EMPTY_TUPLE).to_value();
        }

        unsafe {
            let arena = self.arena.borrow();
            let (avalue, extra) = arena.alloc_extra_non_drop(tuple_avalue(elems.len()));
            MaybeUninit::write_slice(extra, elems);
            Value::new_repr(&*avalue)
        }
    }

    pub(crate) fn alloc_array<'v>(&'v self, cap: usize) -> ValueTyped<'v, Array<'v>> {
        if cap == 0 {
            return FrozenValueTyped::new_repr(VALUE_EMPTY_ARRAY.repr()).to_value_typed();
        }

        unsafe {
            let (avalue, _) = self
                .arena
                .borrow()
                .alloc_extra_non_drop(array_avalue(cap as u32));
            ValueTyped::new_repr(&*avalue)
        }
    }

    pub fn alloc_list<'v>(&'v self, elems: &[Value<'v>]) -> Value<'v> {
        let array = self.alloc_array(elems.len());
        array.extend_from_slice(elems);
        self.alloc_raw(list_avalue(array))
    }

    pub fn alloc_list_iter<'v>(&'v self, elems: impl IntoIterator<Item = Value<'v>>) -> Value<'v> {
        let elems = elems.into_iter();
        let array = self.alloc_array(0);
        let list = self.alloc_raw_typed(list_avalue(array));
        list.0.extend(elems, self);
        list.to_value()
    }

    /// Allocate a list by concatenating two slices.
    pub(crate) fn alloc_list_concat<'v>(&'v self, a: &[Value<'v>], b: &[Value<'v>]) -> Value<'v> {
        let array = self.alloc_array(a.len() + b.len());
        array.extend_from_slice(a);
        array.extend_from_slice(b);
        self.alloc_raw(list_avalue(array))
    }

    pub(crate) fn alloc_char<'v>(&'v self, x: char) -> Value<'v> {
        let mut dst = [0; 4];
        let res = x.encode_utf8(&mut dst);
        self.alloc_str(res)
    }

    pub(crate) fn alloc_float<'v>(&'v self, f: StarlarkFloat) -> Value<'v> {
        self.alloc_raw(float_avalue(f))
    }

    /// Allocate a [`SimpleValue`] on the [`Heap`].
    pub fn alloc_simple<'v, T: SimpleValue>(&'v self, x: T) -> Value<'v> {
        self.alloc_raw(simple(x))
    }

    /// Allocate a [`ComplexValue`] on the [`Heap`].
    pub fn alloc_complex<'v, T>(&'v self, x: T) -> Value<'v>
    where
        T: ComplexValue<'v>,
        T::Frozen: SimpleValue,
    {
        self.alloc_raw(complex(x))
    }

    pub(crate) fn for_each_ordered<'v>(&'v self, mut f: impl FnMut(Value<'v>)) {
        self.arena.borrow_mut().for_each_ordered(|x| {
            // Otherwise the Value is constrainted by the borrow_mut, when
            // we consider values to be kept alive permanently, other than
            // when a GC happens
            f(Value::new_ptr_query_is_str(unsafe {
                cast::ptr_lifetime(x)
            }))
        })
    }

    /// Garbage collect any values that are unused. This function is _unsafe_ in
    /// the sense that any `Value<'v>` not returned by `Tracer` _will become
    /// invalid_. Furthermore, any references to values, e.g `&'v str` will
    /// also become invalid.
    pub(crate) unsafe fn garbage_collect<'v>(&'v self, f: impl FnOnce(&Tracer<'v>)) {
        // Record the highest peak, so it never decreases
        self.peak_allocated.set(self.peak_allocated_bytes());
        self.garbage_collect_internal(f)
    }

    fn garbage_collect_internal<'v>(&'v self, f: impl FnOnce(&Tracer<'v>)) {
        // Must rewrite all Value's so they point at the new heap
        let mut arena = self.arena.borrow_mut();

        let tracer = Tracer::<'v> {
            arena: Arena::default(),
            phantom: PhantomData,
        };
        f(&tracer);
        *arena = tracer.arena;
    }

    /// Obtain a summary of how much memory is currently allocated by this heap.
    pub fn allocated_summary(&self) -> HeapSummary {
        self.arena.borrow().allocated_summary()
    }
}

/// Used to perform garbage collection by [`Trace::trace`](crate::values::Trace::trace).
pub struct Tracer<'v> {
    arena: Arena,
    phantom: PhantomData<&'v ()>,
}

impl<'v> Tracer<'v> {
    /// Walk over a value during garbage collection.
    pub fn trace(&self, value: &mut Value<'v>) {
        *value = self.adjust(*value)
    }

    pub(crate) fn reserve<'a, 'v2: 'v + 'a, T: AValue<'v2, ExtraElem = ()>>(
        &'a self,
    ) -> (Value<'v>, Reservation<'a, 'v2, T>) {
        let (v, r, extra) = self.reserve_with_extra::<T>(0);
        debug_assert!(extra.is_empty());
        (v, r)
    }

    pub(crate) fn reserve_with_extra<'a, 'v2: 'v + 'a, T: AValue<'v2>>(
        &'a self,
        extra_len: usize,
    ) -> (
        Value<'v>,
        Reservation<'a, 'v2, T>,
        &'a mut [MaybeUninit<T::ExtraElem>],
    ) {
        assert!(!T::is_str(), "strings cannot be reserved");
        let (r, extra) = self.arena.reserve_with_extra::<T>(extra_len);
        let v = Value::new_ptr(unsafe { cast::ptr_lifetime(r.ptr()) }, false);
        (v, r, extra)
    }

    pub(crate) fn alloc_str(&self, x: &str) -> Value<'v> {
        let (v, extra) = self.arena.alloc_extra_non_drop(starlark_str(x.len()));
        MaybeUninit::write_slice(extra, x.as_bytes());
        unsafe { transmute!(Value, Value, Value::new_repr(&*v)) }
    }

    fn adjust(&self, value: Value<'v>) -> Value<'v> {
        // Case 1, doesn't point at the old arena
        if !value.0.is_unfrozen() {
            return value;
        }
        let old_val = value.0.unpack_ptr().unwrap();

        // Case 2: We have already been replaced with a forwarding, or need to freeze
        let res = match old_val.unpack_overwrite() {
            Either::Left(x) => Value::new_ptr_usize_with_str_tag(x),
            Either::Right(v) => unsafe {
                v.heap_copy(old_val as *const AValueHeader as *mut AValueHeader, self)
            },
        };

        res
    }
}

#[test]
fn test_send_sync()
where
    FrozenHeapRef: Send + Sync,
{
}
