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

//! Round-trip serialize/deserialize tests for Starlark values.

use allocative::Allocative;
use derive_more::Display;
use pagable::PagableDeserialize;
use pagable::PagableSerialize;
use starlark_derive::NoSerialize;
use starlark_derive::ProvidesStaticType;
use starlark_derive::StarlarkPagable;
use starlark_derive::starlark_value;

use crate as starlark;
use crate::starlark_simple_value;
use crate::values::FrozenHeap;
use crate::values::FrozenHeapRef;
use crate::values::FrozenValue;
use crate::values::StarlarkValue;
use crate::values::layout::heap::heap_type::FrozenHeapName;

/// Private test heap name for pagable tests.
#[derive(Debug, Hash)]
struct TestHeapName(String);

impl TestHeapName {
    fn heap_name(name: &str) -> FrozenHeapName {
        FrozenHeapName::User(Box::new(Self(name.to_owned())))
    }
}

/// A simple test type with primitive fields.
#[derive(
    Debug,
    Display,
    Allocative,
    ProvidesStaticType,
    NoSerialize,
    StarlarkPagable
)]
#[display("SimpleData({}, {})", self.flag, self.count)]
struct SimpleData {
    flag: bool,
    count: usize,
}

starlark_simple_value!(SimpleData);

#[starlark_value(type = "SimpleData", skip_pagable)]
impl<'v> StarlarkValue<'v> for SimpleData {
    type Canonical = Self;
}

fn round_trip_heap_ref(heap_ref: &FrozenHeapRef) -> crate::Result<FrozenHeapRef> {
    let mut ser = pagable::testing::TestingSerializer::new();
    heap_ref
        .pagable_serialize(&mut ser)
        .map_err(crate::Error::new_other)?;
    let bytes = ser.finish();

    let mut de = pagable::testing::TestingDeserializer::new(&bytes);
    let restored = FrozenHeapRef::pagable_deserialize(&mut de).map_err(crate::Error::new_other)?;
    Ok(restored)
}

/// A test type with rust heap-allocated fields (Vec, Box, String).
#[derive(
    Debug,
    Display,
    Allocative,
    ProvidesStaticType,
    NoSerialize,
    StarlarkPagable
)]
#[display("HeapData({:?}, {:?}, {:?})", self.items, self.label, self.boxed)]
struct HeapData {
    items: Vec<u32>,
    label: String,
    boxed: Box<i64>,
}

starlark_simple_value!(HeapData);

#[starlark_value(type = "HeapData", skip_pagable)]
impl<'v> StarlarkValue<'v> for HeapData {
    type Canonical = Self;
}

#[test]
fn test_simple_value_round_trip() -> crate::Result<()> {
    // 1. Create heap with a SimpleData value.
    let heap = FrozenHeap::new();
    heap.alloc_simple(SimpleData {
        flag: true,
        count: 42,
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test_simple_value"));

    // 2. Round-trip via pagable serialize/deserialize.
    let restored = round_trip_heap_ref(&heap_ref)?;

    // 3. Verify: downcast to typed value and check fields.
    let headers = restored.collect_undrop_headers_ordered();
    assert_eq!(headers.len(), 1);
    let avalue = headers[0].unpack();
    let data: &SimpleData = avalue.downcast_ref().unwrap();
    assert_eq!(data.flag, true);
    assert_eq!(data.count, 42);

    Ok(())
}

#[test]
fn test_heap_allocated_value_round_trip() -> crate::Result<()> {
    // 1. Create heap with a HeapData value containing Vec, String, Box.
    let heap = FrozenHeap::new();
    heap.alloc_simple(HeapData {
        items: vec![10, 20, 30],
        label: "hello".to_owned(),
        boxed: Box::new(-99),
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test_heap_data_round_trip"));

    // 2. Round-trip via pagable serialize/deserialize.
    let restored = round_trip_heap_ref(&heap_ref)?;

    // 3. Verify: downcast to typed value and check fields.
    // HeapData has Drop (Vec, String, Box), so it's in the drop bump.
    let headers = restored.collect_drop_headers_ordered();
    assert_eq!(headers.len(), 1);
    let avalue = headers[0].unpack();
    let data: &HeapData = avalue.downcast_ref().unwrap();
    assert_eq!(data.items, vec![10, 20, 30]);
    assert_eq!(data.label, "hello");
    assert_eq!(*data.boxed, -99);

    Ok(())
}

/// A test type with a FrozenValue field that references another value in the same heap.
#[derive(
    Debug,
    Display,
    Allocative,
    ProvidesStaticType,
    NoSerialize,
    StarlarkPagable
)]
#[display("RefData({})", self.label)]
struct RefData {
    label: usize,
    target: FrozenValue,
}

starlark_simple_value!(RefData);

#[starlark_value(type = "RefData", skip_pagable)]
impl<'v> StarlarkValue<'v> for RefData {
    type Canonical = Self;
}

#[test]
fn test_frozen_value_ref_round_trip() -> crate::Result<()> {
    // 1. Create heap with a SimpleData value, then a RefData pointing to it.
    let heap = FrozenHeap::new();
    let target_fv = heap.alloc_simple(SimpleData {
        flag: true,
        count: 99,
    });
    heap.alloc_simple(RefData {
        label: 7,
        target: target_fv,
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    // 2. Round-trip via pagable serialize/deserialize.
    let restored = round_trip_heap_ref(&heap_ref)?;

    // 3. Verify: both values are in the undrop bump (neither needs Drop).
    let headers = restored.collect_undrop_headers_ordered();
    assert_eq!(headers.len(), 2);

    // First value should be the SimpleData target.
    let target_data: &SimpleData = headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(target_data.flag, true);
    assert_eq!(target_data.count, 99);

    // Second value should be the RefData with a FrozenValue pointing at the target.
    let ref_data: &RefData = headers[1].unpack().downcast_ref().unwrap();
    assert_eq!(ref_data.label, 7);

    // The FrozenValue in RefData should point to the restored SimpleData.
    let resolved: &SimpleData = ref_data
        .target
        .downcast_frozen_ref::<SimpleData>()
        .expect("FrozenValue should point to SimpleData")
        .value;
    assert_eq!(resolved.flag, true);
    assert_eq!(resolved.count, 99);

    // Verify pointer identity: the FrozenValue should point to the same header.
    let target_header_addr = headers[0] as *const _ as usize;
    let fv_ptr = ref_data.target.ptr_value().ptr_value_untagged();
    assert_eq!(fv_ptr, target_header_addr);

    Ok(())
}

/// A test type with Drop (due to Vec) that holds a FrozenValue reference.
#[derive(
    Debug,
    Display,
    Allocative,
    ProvidesStaticType,
    NoSerialize,
    StarlarkPagable
)]
#[display("DropRefData({:?})", self.items)]
struct DropRefData {
    items: Vec<u32>,
    target: FrozenValue,
}

starlark_simple_value!(DropRefData);

#[starlark_value(type = "DropRefData", skip_pagable)]
impl<'v> StarlarkValue<'v> for DropRefData {
    type Canonical = Self;
}

#[test]
fn test_frozen_value_drop_to_undrop_round_trip() -> crate::Result<()> {
    // DropRefData (drop bump) references SimpleData (undrop bump).
    let heap = FrozenHeap::new();
    let target_fv = heap.alloc_simple(SimpleData {
        flag: false,
        count: 123,
    });
    heap.alloc_simple(DropRefData {
        items: vec![1, 2, 3],
        target: target_fv,
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    // DropRefData is in the drop bump.
    let drop_headers = restored.collect_drop_headers_ordered();
    assert_eq!(drop_headers.len(), 1);
    let drop_ref_data: &DropRefData = drop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(drop_ref_data.items, vec![1, 2, 3]);

    // SimpleData is in the undrop bump.
    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 1);
    let target_data: &SimpleData = undrop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(target_data.flag, false);
    assert_eq!(target_data.count, 123);

    // The FrozenValue in DropRefData should point to the restored SimpleData.
    let resolved: &SimpleData = drop_ref_data
        .target
        .downcast_frozen_ref::<SimpleData>()
        .expect("FrozenValue should point to SimpleData")
        .value;
    assert_eq!(resolved.flag, false);
    assert_eq!(resolved.count, 123);

    // Pointer identity check.
    let target_header_addr = undrop_headers[0] as *const _ as usize;
    let fv_ptr = drop_ref_data.target.ptr_value().ptr_value_untagged();
    assert_eq!(fv_ptr, target_header_addr);

    Ok(())
}

#[test]
fn test_frozen_value_undrop_to_drop_round_trip() -> crate::Result<()> {
    // RefData (undrop bump) references HeapData (drop bump).
    let heap = FrozenHeap::new();
    let target_fv = heap.alloc_simple(HeapData {
        items: vec![10, 20],
        label: "target".to_owned(),
        boxed: Box::new(42),
    });
    heap.alloc_simple(RefData {
        label: 5,
        target: target_fv,
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    // HeapData is in the drop bump.
    let drop_headers = restored.collect_drop_headers_ordered();
    assert_eq!(drop_headers.len(), 1);
    let target_data: &HeapData = drop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(target_data.items, vec![10, 20]);
    assert_eq!(target_data.label, "target");
    assert_eq!(*target_data.boxed, 42);

    // RefData is in the undrop bump.
    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 1);
    let ref_data: &RefData = undrop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(ref_data.label, 5);

    // The FrozenValue in RefData should point to the restored HeapData.
    let resolved: &HeapData = ref_data
        .target
        .downcast_frozen_ref::<HeapData>()
        .expect("FrozenValue should point to HeapData")
        .value;
    assert_eq!(resolved.items, vec![10, 20]);
    assert_eq!(resolved.label, "target");
    assert_eq!(*resolved.boxed, 42);

    // Pointer identity check.
    let target_header_addr = drop_headers[0] as *const _ as usize;
    let fv_ptr = ref_data.target.ptr_value().ptr_value_untagged();
    assert_eq!(fv_ptr, target_header_addr);

    Ok(())
}

#[test]
fn test_frozen_list_round_trip() -> crate::Result<()> {
    use crate::values::list::value::ListGen;
    use crate::values::types::list::value::FrozenListData;

    // Create a heap with SimpleData values and a frozen list referencing them.
    let heap = FrozenHeap::new();
    let a = heap.alloc_simple(SimpleData {
        flag: true,
        count: 10,
    });
    let b = heap.alloc_simple(SimpleData {
        flag: false,
        count: 20,
    });
    heap.alloc_list(&[a, b]);
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    // All three values (2 SimpleData + 1 list) are in the undrop bump (no Drop).
    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 3);

    let a_data: &SimpleData = undrop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(a_data.flag, true);
    assert_eq!(a_data.count, 10);

    let b_data: &SimpleData = undrop_headers[1].unpack().downcast_ref().unwrap();
    assert_eq!(b_data.flag, false);
    assert_eq!(b_data.count, 20);

    // Third header is the list.
    let list_value: &ListGen<FrozenListData> = undrop_headers[2].unpack().downcast_ref().unwrap();
    let content = list_value.0.content();
    assert_eq!(content.len(), 2);

    // Verify list elements point to the restored SimpleData values.
    let elem_a: &SimpleData = content[0]
        .downcast_frozen_ref::<SimpleData>()
        .expect("element 0 should be SimpleData")
        .value;
    assert_eq!(elem_a.flag, true);
    assert_eq!(elem_a.count, 10);

    let elem_b: &SimpleData = content[1]
        .downcast_frozen_ref::<SimpleData>()
        .expect("element 1 should be SimpleData")
        .value;
    assert_eq!(elem_b.flag, false);
    assert_eq!(elem_b.count, 20);

    // Pointer identity: list elements should point to the same headers.
    assert_eq!(
        content[0].ptr_value().ptr_value_untagged(),
        undrop_headers[0] as *const _ as usize
    );
    assert_eq!(
        content[1].ptr_value().ptr_value_untagged(),
        undrop_headers[1] as *const _ as usize
    );

    Ok(())
}

#[test]
fn test_frozen_tuple_round_trip() -> crate::Result<()> {
    use crate::values::types::tuple::value::FrozenTuple;

    // Create a heap with SimpleData values and a frozen tuple referencing them.
    let heap = FrozenHeap::new();
    let a = heap.alloc_simple(SimpleData {
        flag: true,
        count: 100,
    });
    let b = heap.alloc_simple(SimpleData {
        flag: false,
        count: 200,
    });
    heap.alloc_tuple(&[a, b]);
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    // All three values (2 SimpleData + 1 tuple) are in the undrop bump.
    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 3);

    let a_data: &SimpleData = undrop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(a_data.flag, true);
    assert_eq!(a_data.count, 100);

    let b_data: &SimpleData = undrop_headers[1].unpack().downcast_ref().unwrap();
    assert_eq!(b_data.flag, false);
    assert_eq!(b_data.count, 200);

    // Third header is the tuple.
    let tuple_value: &FrozenTuple = undrop_headers[2].unpack().downcast_ref().unwrap();
    let content = tuple_value.content();
    assert_eq!(content.len(), 2);

    // Verify tuple elements point to the restored SimpleData values.
    let elem_a: &SimpleData = content[0]
        .downcast_frozen_ref::<SimpleData>()
        .expect("element 0 should be SimpleData")
        .value;
    assert_eq!(elem_a.flag, true);
    assert_eq!(elem_a.count, 100);

    let elem_b: &SimpleData = content[1]
        .downcast_frozen_ref::<SimpleData>()
        .expect("element 1 should be SimpleData")
        .value;
    assert_eq!(elem_b.flag, false);
    assert_eq!(elem_b.count, 200);

    // Pointer identity check.
    assert_eq!(
        content[0].ptr_value().ptr_value_untagged(),
        undrop_headers[0] as *const _ as usize
    );
    assert_eq!(
        content[1].ptr_value().ptr_value_untagged(),
        undrop_headers[1] as *const _ as usize
    );

    Ok(())
}

#[test]
fn test_frozen_str_value_round_trip() -> crate::Result<()> {
    use crate::values::string::str_type::StarlarkStr;

    // RefData (undrop) holds a FrozenValue pointing to a frozen string (also undrop).
    // Strings with len > 1 are heap-allocated with StrFrozen tag.
    let heap = FrozenHeap::new();
    let str_fv = heap.alloc_str("hello world").to_frozen_value();
    heap.alloc_simple(RefData {
        label: 42,
        target: str_fv,
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    // Both the string and RefData are in the undrop bump.
    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 2);

    // First header is the string.
    let restored_str = undrop_headers[0]
        .unpack()
        .downcast_ref::<StarlarkStr>()
        .unwrap();
    assert_eq!(restored_str.as_str(), "hello world");

    // Second header is the RefData.
    let ref_data: &RefData = undrop_headers[1].unpack().downcast_ref().unwrap();
    assert_eq!(ref_data.label, 42);

    // The FrozenValue should be a string (is_str tag set).
    assert!(ref_data.target.is_str());
    assert_eq!(ref_data.target.unpack_str().unwrap(), "hello world");

    // Pointer identity check.
    assert_eq!(
        ref_data.target.ptr_value().ptr_value_untagged(),
        undrop_headers[0] as *const _ as usize
    );

    Ok(())
}

#[test]
fn test_frozen_value_inline_int_round_trip() -> crate::Result<()> {
    // RefData holds a FrozenValue that is an inline integer (not a heap pointer).
    let heap = FrozenHeap::new();
    let int_fv = FrozenValue::testing_new_int(42);
    heap.alloc_simple(RefData {
        label: 1,
        target: int_fv,
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 1);

    let ref_data: &RefData = undrop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(ref_data.label, 1);
    assert_eq!(ref_data.target.unpack_i32(), Some(42));

    Ok(())
}

#[test]
fn test_cross_heap_frozen_value_round_trip() -> crate::Result<()> {
    // Create a "dependency" heap with a SimpleData value.
    let dep_heap = FrozenHeap::new();
    let dep_fv = dep_heap.alloc_simple(SimpleData {
        flag: true,
        count: 77,
    });
    let dep_heap_ref = dep_heap.into_ref_named(TestHeapName::heap_name("dep"));

    // Create a "main" heap that references the dep heap.
    let main_heap = FrozenHeap::new();
    main_heap.add_reference(&dep_heap_ref);

    main_heap.alloc_simple(RefData {
        label: 99,
        target: dep_fv,
    });
    let main_heap_ref = main_heap.into_ref_named(TestHeapName::heap_name("main"));

    // Round-trip the main heap (which has a ref to dep heap).
    let restored = round_trip_heap_ref(&main_heap_ref)?;

    // The main heap should have 1 value (RefData) in undrop.
    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 1);

    let ref_data: &RefData = undrop_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(ref_data.label, 99);

    // The FrozenValue should resolve to a SimpleData with the dep heap's data.
    let resolved: &SimpleData = ref_data
        .target
        .downcast_frozen_ref::<SimpleData>()
        .expect("FrozenValue should point to SimpleData in dep heap")
        .value;
    assert_eq!(resolved.flag, true);
    assert_eq!(resolved.count, 77);

    // The main heap should have 1 ref (the dep heap).
    let refs: Vec<_> = restored.refs().collect();
    assert_eq!(refs.len(), 1);

    // Pointer identity: the FrozenValue should point into the restored dep heap's first value.
    let restored_dep_headers = refs[0].collect_undrop_headers_ordered();
    assert_eq!(restored_dep_headers.len(), 1);
    assert_eq!(
        ref_data.target.ptr_value().ptr_value_untagged(),
        restored_dep_headers[0] as *const _ as usize
    );

    Ok(())
}

#[test]
fn test_heap_ref_dedup_round_trip() -> crate::Result<()> {
    // Diamond dependency: heap_a refs [heap_b, heap_c], both heap_b and heap_c ref heap_d. (A → [B, C] → D)
    // After round-trip, the deserialized heap_b and heap_c should share the same heap_d ref.

    // heap_d: shared dependency.
    let heap_d = FrozenHeap::new();
    let d_fv = heap_d.alloc_simple(SimpleData {
        flag: true,
        count: 1,
    });
    let heap_d_ref = heap_d.into_ref_named(TestHeapName::heap_name("d"));

    // heap_b: depends on heap_d, has a value referencing heap_d.
    let heap_b = FrozenHeap::new();
    heap_b.add_reference(&heap_d_ref);
    heap_b.alloc_simple(RefData {
        label: 2,
        target: d_fv,
    });
    let heap_b_ref = heap_b.into_ref_named(TestHeapName::heap_name("b"));

    // heap_c: also depends on heap_d, has a value referencing heap_d.
    let heap_c = FrozenHeap::new();
    heap_c.add_reference(&heap_d_ref);
    heap_c.alloc_simple(RefData {
        label: 3,
        target: d_fv,
    });
    let heap_c_ref = heap_c.into_ref_named(TestHeapName::heap_name("c"));

    // heap_a: depends on both heap_b and heap_c.
    let heap_a = FrozenHeap::new();
    heap_a.add_reference(&heap_b_ref);
    heap_a.add_reference(&heap_c_ref);
    heap_a.alloc_simple(SimpleData {
        flag: false,
        count: 4,
    });
    let heap_a_ref = heap_a.into_ref_named(TestHeapName::heap_name("a"));

    let restored = round_trip_heap_ref(&heap_a_ref)?;

    // heap_a has 2 refs: heap_b and heap_c.
    let a_refs: Vec<_> = restored.refs().collect();
    assert_eq!(a_refs.len(), 2);

    let restored_b = &a_refs[0];
    let restored_c = &a_refs[1];

    // Both heap_b and heap_c should have 1 ref each (heap_d).
    let b_refs: Vec<_> = restored_b.refs().collect();
    let c_refs: Vec<_> = restored_c.refs().collect();
    assert_eq!(b_refs.len(), 1);
    assert_eq!(c_refs.len(), 1);

    // The key dedup check: heap_b's ref to heap_d and heap_c's ref to heap_d
    // should be the same FrozenHeapRef (pointer-equal via Arc).
    assert_eq!(b_refs[0], c_refs[0]);

    // Verify the shared heap_d's value is correct.
    let d_headers = b_refs[0].collect_undrop_headers_ordered();
    assert_eq!(d_headers.len(), 1);
    let d_data: &SimpleData = d_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(d_data.flag, true);
    assert_eq!(d_data.count, 1);

    // Verify heap_b's and heap_c's values point into the shared heap_d.
    let b_headers = restored_b.collect_undrop_headers_ordered();
    assert_eq!(b_headers.len(), 1);
    let b_data: &RefData = b_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(b_data.label, 2);
    assert_eq!(
        b_data.target.ptr_value().ptr_value_untagged(),
        d_headers[0] as *const _ as usize
    );

    let c_headers = restored_c.collect_undrop_headers_ordered();
    assert_eq!(c_headers.len(), 1);
    let c_data: &RefData = c_headers[0].unpack().downcast_ref().unwrap();
    assert_eq!(c_data.label, 3);
    assert_eq!(
        c_data.target.ptr_value().ptr_value_untagged(),
        d_headers[0] as *const _ as usize
    );

    Ok(())
}

#[test]
fn test_frozen_value_typed_round_trip() -> crate::Result<()> {
    use crate::values::FrozenValueTyped;

    // Create a heap with a SimpleData, then wrap it as FrozenValueTyped.
    let heap = FrozenHeap::new();
    let fv = heap.alloc_simple(SimpleData {
        flag: true,
        count: 77,
    });
    let typed = FrozenValueTyped::<SimpleData>::new(fv).unwrap();

    // Create a RefData that holds the typed value as a plain FrozenValue.
    // This exercises FrozenValueTyped's StarlarkSerialize (which delegates to FrozenValue).
    heap.alloc_simple(RefData {
        label: 3,
        target: typed.to_frozen_value(),
    });
    let heap_ref = heap.into_ref_named(TestHeapName::heap_name("test_fvt"));

    let restored = round_trip_heap_ref(&heap_ref)?;

    let undrop_headers = restored.collect_undrop_headers_ordered();
    assert_eq!(undrop_headers.len(), 2);

    // Verify the target FrozenValue can be downcast back to SimpleData via FrozenValueTyped.
    let ref_data: &RefData = undrop_headers[1].unpack().downcast_ref().unwrap();
    let restored_typed = FrozenValueTyped::<SimpleData>::new(ref_data.target).unwrap();
    assert_eq!(restored_typed.flag, true);
    assert_eq!(restored_typed.count, 77);

    Ok(())
}
