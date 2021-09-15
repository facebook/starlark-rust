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

//! The values module define a trait `StarlarkValue` that defines the attribute of
//! any value in Starlark and a few macro to help implementing this trait.
//! The `Value` struct defines the actual structure holding a StarlarkValue. It is
//! mostly used to enable mutable and Rc behavior over a StarlarkValue.
//! This modules also defines this traits for the basic immutable values: int,
//! bool and NoneType. Sub-modules implement other common types of all Starlark
//! dialect.
//!
//! __Note__: we use _sequence_, _iterable_ and _indexable_ according to the
//! definition in the [Starlark specification](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#sequence-types).
//! We also use the term _container_ for denoting any of those type that can
//! hold several values.
use crate::{
    codemap::Span,
    collections::SmallMap,
    environment::Globals,
    eval::{Arguments, Evaluator},
    values::{
        docs::DocItem, function::FUNCTION_TYPE, ControlError, Freezer, FrozenStringValue, Heap,
        Tracer, Value, ValueError,
    },
};
use gazebo::any::AnyLifetime;
use std::{
    any::TypeId,
    cell::{Cell, RefCell},
    cmp::Ordering,
    fmt::{Debug, Write},
};

/// Called by the garbage collection, and must walk over every contained `Value` in the type.
/// Marked `unsafe` because if you miss a nested `Value`, it will probably segfault.
pub unsafe trait Trace<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>);
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for Vec<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.iter_mut().for_each(|x| x.trace(tracer));
    }
}

unsafe impl<'v, K: Trace<'v>, V: Trace<'v>> Trace<'v> for SmallMap<K, V> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.iter_mut().for_each(|(k, v)| {
            // We are going to replace it, but promise morally it's the same Value
            // so things like Hash/Ord/Eq will work the same
            #[allow(clippy::cast_ref_to_mut)]
            let k_mut = unsafe { &mut *(k as *const K as *mut K) };
            k_mut.trace(tracer);
            v.trace(tracer);
        })
    }
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for Option<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        if let Some(x) = self {
            x.trace(tracer)
        }
    }
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for RefCell<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.get_mut().trace(tracer)
    }
}

unsafe impl<'v, T: Trace<'v> + Copy> Trace<'v> for Cell<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        let mut v = self.get();
        v.trace(tracer);
        self.set(v)
    }
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for Box<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        Box::as_mut(self).trace(tracer)
    }
}

unsafe impl<'v, T1: Trace<'v>, T2: Trace<'v>> Trace<'v> for (T1, T2) {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.0.trace(tracer);
        self.1.trace(tracer);
    }
}

unsafe impl<'v> Trace<'v> for Value<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        tracer.trace(self)
    }
}

unsafe impl<'v> Trace<'v> for String {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for usize {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for i32 {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for u32 {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for bool {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

unsafe impl<'v> Trace<'v> for std::time::Instant {
    fn trace(&mut self, _tracer: &Tracer<'v>) {}
}

/// A trait for values which are more complex - because they are either mutable,
/// or contain references to other values.
///
/// For values that contain nested [`Value`] types (mutable or not) there are a bunch of helpers
/// and macros.
///
/// ## Types containing [`Value`]
///
/// A Starlark type containing values will need to exist in two states: one containing [`Value`]
/// and one containing [`FrozenValue`](crate::values::FrozenValue). To deal with that, if we are defining the type
/// containing a single value, let's call it `One`, we'd define `OneGen`
/// (for the general version), and then have the [`starlark_complex_value!`] macro
/// generate `One` and `FrozenOne` aliases.
///
/// ```
/// use starlark::values::{AnyLifetime, ComplexValue, Coerce, Freezer, FrozenValue, SimpleValue, StarlarkValue, Value, ValueLike, Trace, Tracer};
/// use starlark::{starlark_complex_value, starlark_type};
///
/// #[derive(Debug, Trace, Coerce)]
/// #[repr(C)]
/// struct OneGen<V>(V);
/// starlark_complex_value!(One);
///
/// impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for OneGen<V>
///     where Self: AnyLifetime<'v>
/// {
///     starlark_type!("one");
///
///     // To implement methods which are work for both `One` and `FrozenOne`,
///     // use the `ValueLike` trait.
/// }
///
/// impl<'v> ComplexValue<'v> for One<'v> {
///     type Frozen = FrozenOne;
///     fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
///         Ok(OneGen(self.0.freeze(freezer)?))
///     }
/// }
/// ```
///
/// The [`starlark_complex_value!`] requires that the type have an instance for `Coerce`,
/// then the macro defines two type aliases.
///
/// ```
/// # use crate::starlark::values::*;
/// # #[derive(Debug, Trace)]
/// # struct OneGen<V>(V);
/// type One<'v> = OneGen<Value<'v>>;
/// type FrozenOne = OneGen<FrozenValue>;
/// ```
///
/// To make these aliases public (or public to the crate) pass a visibility
/// to the macro, e.g. `starlark_complex_value!(pub One)`.
///
/// The macro also defines instances of [`AnyLifetime`] for both,
/// [`AllocValue`](crate::values::AllocValue) for both,
/// [`AllocFrozenValue`](crate::values::AllocFrozenValue) for the frozen one,
/// [`SimpleValue`] for the frozen one and
/// [`FromValue`](crate::values::FromValue) for the non-frozen one.
/// It also defines the methods:
///
/// ```
/// # use crate::starlark::values::*;
/// # use std::cell::RefMut;
/// # struct OneGen<V>(V);
/// # type One<'v> = OneGen<Value<'v>>;
/// impl<'v> One<'v> {
///     // Obtain a reference to `One` from a `Value`, regardless
///     // of whether the underlying `Value` is a `One` or `FrozenOne`.
///     pub fn from_value(x: Value<'v>) -> Option<ARef<'v, Self>> {
/// # unimplemented!(
/// # r#"
///         ...
/// # "#);
///     }
/// }
/// ```
///
/// ## Different types
///
/// If the types are different between the frozen and non-frozen values you can define your own
/// type specialisations as `type One<'v> = OneGen<Value<'v>>` and `type FrozenOne = OneGen<String>`
/// and use [`starlark_complex_values!`] which will provide similar facilities to [`starlark_complex_value!`].
///
/// ## Other types
///
/// The macro [`starlark_complex_value!`] is applicable when there is a single base type,
/// `FooGen<V>`, with specialisations `FooGen<Value<'v>>` and `FooGen<FrozenValue>`.
/// If you have a type where the difference between frozen and non-frozen does not follow this
/// pattern then you will have to write instances of the traits you need manually.
/// Examples of cases where the macro doesn't work include:
///
/// * If your type doesn't contain any [`Value`] types, but instead implements this trait for mutability.
/// * If the difference between frozen and non-frozen is more complex, e.g. a [`Cell`](std::cell::Cell)
///   when non-frozen and a direct value when frozen.
pub trait ComplexValue<'v>: StarlarkValue<'v> + Trace<'v> {
    type Frozen: SimpleValue;

    /// Freeze a value. The frozen value _must_ be equal to the original,
    /// and produce the same hash.
    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen>;
}

/// A trait representing Starlark values which are simple - they
/// aren't mutable and can't contain other Starlark values.
///
/// Let's define a simple object, where `+x` makes the string uppercase:
///
/// ```
/// use starlark::values::{Heap, StarlarkValue, Value};
/// use starlark::{starlark_simple_value, starlark_type};
///
/// #[derive(Debug)]
/// struct MyObject(String);
/// starlark_simple_value!(MyObject);
/// impl<'v> StarlarkValue<'v> for MyObject {
///     starlark_type!("my_object");
///
///     // We can choose to implement whichever methods we want.
///     // All other operations will result in runtime errors.
///     fn plus(&self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
///         Ok(heap.alloc(MyObject(self.0.to_uppercase())))
///     }
/// }
/// ```
///
/// The [`starlark_simple_value!`] macro defines instances of [`AnyLifetime`],
/// [`AllocValue`](crate::values::AllocValue),
/// [`AllocFrozenValue`](crate::values::AllocFrozenValue), [`SimpleValue`] and
/// [`FromValue`](crate::values::FromValue). It also defines a method:
///
/// ```
/// # use crate::starlark::values::*;
/// # struct MyObject;
/// impl MyObject {
///     pub fn from_value<'v>(x: Value<'v>) -> Option<ARef<'v, MyObject>> {
/// # unimplemented!(
/// # r#"
///         ...
/// # "#);
///     }
/// }
/// ```
///
/// All users defining [`SimpleValue`] should use this macro.
pub trait SimpleValue: StarlarkValue<'static> + Send + Sync {}

/// How to put a Rust values into [`Value`]s.
///
/// Every Rust value stored in a [`Value`] must implement this trait, along with
/// either [`SimpleValue`] or [`ComplexValue`]. You _must_ implement [`ComplexValue`] if:
///
/// * A type is _mutable_, if you ever need to get a `&mut self` reference to it.
/// * A type _contains_ nested Starlark [`Value`]s.
///
/// Otherwise you should implement [`SimpleValue`].
/// See those two traits for examples of how to implement them.
///
/// There are only two required methods of [`StarlarkValue`], namely
/// [`get_type`](StarlarkValue::get_type)
/// and [`get_type_value_static`](StarlarkValue::get_type_value_static).
/// Both these should be implemented with the [`starlark_type!`] macro:
///
/// ```
/// use starlark::values::StarlarkValue;
/// # use starlark::starlark_simple_value;
/// use starlark::starlark_type;
///
/// #[derive(Debug)]
/// struct Foo;
/// # starlark_simple_value!(Foo);
/// impl<'v> StarlarkValue<'v> for Foo {
///     starlark_type!("foo");
/// }
/// ```
///
/// Every additional field enables further features in Starlark. In most cases the default
/// implementation returns an "unimplemented" [`Err`].
///
/// # Note To Implementors
/// Any additional methods that are added to this trait also need to be added to the
/// [`StarlarkValue`] implementation in `crate::values::layout::avalue::Wrapper`. Otherwise,
/// any implementations other than the default implementation will not be run.
pub trait StarlarkValue<'v>: 'v + AnyLifetime<'v> + Debug {
    /// Return a string describing the type of self, as returned by the type()
    /// function.
    ///
    /// Usually implemented by the [`starlark_type!`] macro.
    fn get_type(&self) -> &'static str;

    /// Like [`get_type`](Self::get_type), but returns a reusable [`FrozenStringValue`]
    /// pointer to it. This function deliberately doesn't take a heap,
    /// as it would not be performant to allocate a new value each time.
    ///
    /// Usually implemented by the [`starlark_type!`] macro.
    fn get_type_value_static() -> FrozenStringValue
    where
        Self: Sized;

    /// Is this value a match for a named type. Usually returns `true` for
    /// values matching `get_type`, but might also work for subtypes it implements.
    fn matches_type(&self, ty: &str) -> bool {
        self.get_type() == ty
    }

    /// Get the members associated with this type, accessible via `this_type.x`.
    /// These members will have `dir`/`getattr`/`hasattr` properly implemented,
    /// so it is the preferred way to go if possible. See
    /// [`GlobalsStatic`](crate::environment::GlobalsStatic) for an example of how
    /// to define this method.
    fn get_methods(&self) -> Option<&'static Globals> {
        None
    }

    /// Return structured documentation for self, if available.
    fn documentation(&self) -> Option<DocItem> {
        None
    }

    /// Return a string representation of self, as returned by the repr()
    /// function.
    /// Defaults to the `Debug` instance, but most types should override this method.
    /// In many cases the `repr()` representation will also be a Starlark expression
    /// for creating the value.
    ///
    /// # Examples:
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// repr("test") == '"test"'
    /// repr([1,2,3]) == '[1, 2, 3]'
    /// repr([1,[2,3]]) == '[1, [2, 3]]'
    /// repr([1]) == '[1]'
    /// repr([]) == '[]'
    /// # "#);
    /// ```
    fn collect_repr(&self, collector: &mut String) {
        // Rust won't return Err when writing to a String, so safe unwrap
        write!(collector, "{:?}", self).unwrap()
    }

    /// Convert the type to a JSON string.
    fn to_json(&self) -> anyhow::Result<String> {
        ValueError::unsupported(self, "to_json()")
    }

    /// Convert self to a boolean, as returned by the bool() function.
    /// The default implementation returns [`true`].
    fn to_bool(&self) -> bool {
        // Return `true` by default, because this is default when implementing
        // custom types in Python: https://docs.python.org/release/2.5.2/lib/truth.html
        true
    }

    /// Convert self to a integer value, as returned by the int() function if
    /// the type is numeric (not for string).
    /// Works for int and bool (0 = false, 1 = true).
    fn to_int(&self) -> anyhow::Result<i32> {
        ValueError::unsupported(self, "int()")
    }

    /// Return a hash code for self to be used when self is placed as a key in a Dict.
    /// Return an [`Err`] if there is no hash for this value (e.g. list).
    /// Must be stable between frozen and non-frozen values.
    fn get_hash(&self) -> anyhow::Result<u64> {
        if self.get_type() == FUNCTION_TYPE {
            // The Starlark spec says values of type "function" must be hashable.
            // We could return the address of the function, but that changes
            // with frozen/non-frozen which breaks freeze for Dict.
            // We could create an atomic counter and use that, but it takes memory,
            // effort, complexity etc, and we don't expect many Dict's keyed by
            // function. Returning 0 as the hash is valid, as Eq will sort it out.
            Ok(0)
        } else {
            Err(ControlError::NotHashableValue(self.get_type().to_owned()).into())
        }
    }

    /// Return how much extra memory is consumed by this data type, in bytes, in addition to the
    /// direct `size_of` measurements. Used for profiling, so best effort rather than precise. Defaults to 0.
    /// Should not reported any memory held on to by a [`Value`].
    fn extra_memory(&self) -> usize {
        0
    }

    /// Compare `self` with `other` for equality.
    /// Should only return an error on excessive recursion.
    fn equals(&self, _other: Value<'v>) -> anyhow::Result<bool> {
        // Type is only equal via a pointer
        Ok(false)
    }

    /// Compare `self` with `other`.
    /// This method returns a result of type [`Ordering`], or an [`Err`]
    /// if the two types differ.
    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        ValueError::unsupported_with(self, "compare", other)
    }

    /// Directly invoke a function.
    /// The number of `named` and `names` arguments are guaranteed to be equal.
    /// A direct implementation is responsible for calling [`Evaluator::with_call_stack`] to ensure
    /// the call stack is properly updated.
    fn invoke(
        &self,
        _me: Value<'v>,
        _location: Option<Span>,
        _args: Arguments<'v, '_>,
        _eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported(self, "call()")
    }

    /// Return the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "[]", index)
    }

    /// Extract a slice of the underlying object if the object is indexable. The
    /// result will be object between `start` and `stop` (both of them are
    /// added length() if negative and then clamped between 0 and length()).
    /// `stride` indicates the direction.
    ///
    /// # Parameters
    ///
    /// * start: the start of the slice.
    /// * stop: the end of the slice.
    /// * stride: the direction of slice,
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 'abc'[1:] == 'bc'         # Remove the first element
    /// 'abc'[:-1] == 'ab'        # Remove the last element
    /// 'abc'[1:-1] == 'b'        # Remove the first and the last element
    /// 'abc'[-1:] == 'c'         # Take the last letter
    /// 'abc'[:1] == 'a'          # Take the first letter
    /// 'banana'[1::2] == 'aaa'   # Select one element out of 2, skipping the first
    /// 'banana'[4::-2] == 'nnb'  # Select one element out of 2 in reverse order, starting at index 4
    /// # "#);
    /// ```
    fn slice(
        &self,
        _start: Option<Value<'v>>,
        _stop: Option<Value<'v>>,
        _stride: Option<Value<'v>>,
        _heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported(self, "[::]")
    }

    /// Returns an iterable over the value of this container if this value holds
    /// an iterable container.
    fn iterate<'a>(
        &'a self,
        _heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'a>>
    where
        'v: 'a,
    {
        ValueError::unsupported(self, "(iter)")
    }

    /// Call a function with the same iterator as would be returned from [`iterate`](StarlarkValue::iterate).
    /// The one advantage is that the iterator does not need to be allocated in a [`Box`].
    /// If you implement this function you must also implement [`iterate`](StarlarkValue::iterate),
    /// but the reverse is not true (this function has a sensible default).
    fn with_iterator(
        &self,
        heap: &'v Heap,
        f: &mut dyn FnMut(&mut dyn Iterator<Item = Value<'v>>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        f(&mut *self.iterate(heap)?)
    }

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> anyhow::Result<i32> {
        ValueError::unsupported(self, "len()")
    }

    /// Get an attribute for the current value as would be returned by dotted
    /// expression (i.e. `a.attribute`).
    ///
    /// The three methods [`get_attr`](StarlarkValue::get_attr),
    /// [`has_attr`](StarlarkValue::has_attr) and [`dir_attr`](StarlarkValue::dir_attr)
    /// must be consistent - if you implement one, you should probably implement all three.
    ///
    /// This operations must have no side effects, because it can be called speculatively.
    fn get_attr(&self, _attribute: &str, _heap: &'v Heap) -> Option<Value<'v>> {
        None
    }

    /// Return true if an attribute of name `attribute` exists for the current
    /// value.
    ///
    /// The three methods [`get_attr`](StarlarkValue::get_attr),
    /// [`has_attr`](StarlarkValue::has_attr) and [`dir_attr`](StarlarkValue::dir_attr)
    /// must be consistent - if you implement one, you should probably implement all three.
    fn has_attr(&self, _attribute: &str) -> bool {
        false
    }

    /// Return a vector of string listing all attribute of the current value.
    ///
    /// The three methods [`get_attr`](StarlarkValue::get_attr),
    /// [`has_attr`](StarlarkValue::has_attr) and [`dir_attr`](StarlarkValue::dir_attr)
    /// must be consistent - if you implement one, you should probably implement all three.
    fn dir_attr(&self) -> Vec<String> {
        Vec::new()
    }

    /// Tell wether `other` is in the current value, if it is a container.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// ('a' in 'abc') == True
    /// ('b' in 'abc') == True
    /// ('z' in 'abc') == False
    /// # "#);
    /// ```
    fn is_in(&self, other: Value<'v>) -> anyhow::Result<bool> {
        ValueError::unsupported_owned(other.get_type(), "in", Some(self.get_type()))
    }

    /// Apply the `+` unary operator to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// +1 == 1
    /// # "#);
    /// ```
    fn plus(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported(self, "+")
    }

    /// Apply the `-` unary operator to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// -(1) == -1
    /// # "#);
    /// ```
    fn minus(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported(self, "-")
    }

    /// Add with the arguments the other way around. Should return [`None`]
    /// to fall through to normal add.
    fn radd(&self, _lhs: Value<'v>, _heap: &'v Heap) -> Option<anyhow::Result<Value<'v>>> {
        None
    }

    /// Add `other` to the current value. Pass both self and
    /// the Value form of self as original.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 1 + 2 == 3
    /// [1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
    /// 'abc' + 'def' == 'abcdef'
    /// (1, 2, 3) + (2, 3) == (1, 2, 3, 2, 3)
    /// # "#);
    /// ```
    fn add(&self, rhs: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "+", rhs)
    }

    /// Substract `other` from the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 1 - 2 == -1
    /// # "#);
    /// ```
    fn sub(&self, other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "-", other)
    }

    /// Multiply the current value with `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 2 * 3 == 6
    /// [1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
    /// 'abc' * 3 == 'abcabcabc'
    /// (1, 2, 3) * 3 == (1, 2, 3, 1, 2, 3, 1, 2, 3)
    /// # "#);
    /// ```
    fn mul(&self, other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "*", other)
    }

    /// Apply the percent operator between the current value and `other`. Usually used on
    /// strings, as per
    /// [the Starlark spec](https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#string-interpolation).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 5 % 3 == 2
    /// "a %s c" % 3 == "a 3 c"
    /// "Hello %s, your score is %d" % ("Bob", 75) == "Hello Bob, your score is 75"
    /// "%d %o %x" % (65, 65, 65) == "65 101 41"
    /// "Hello %s, welcome" % "Bob" == "Hello Bob, welcome"
    /// "%s" % (1,) == "1"
    /// "%s" % ((1,),) == "(1,)"
    /// "%s" % [1] == "[1]"
    /// "test" % () == "test"
    /// # "#);
    /// ```
    fn percent(&self, other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "%", other)
    }

    /// Floor division between the current value and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 7 // 2 == 3
    /// # "#);
    /// ```
    fn floor_div(&self, other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "//", other)
    }

    /// Bitwise `&` operator.
    fn bit_and(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "&", other)
    }

    /// Bitwise `|` operator.
    fn bit_or(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "|", other)
    }

    /// Bitwise `^` operator.
    fn bit_xor(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "^", other)
    }

    /// Bitwise `<<` operator.
    fn left_shift(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, "<<", other)
    }

    /// Bitwise `>>` operator.
    fn right_shift(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        ValueError::unsupported_with(self, ">>", other)
    }

    /// Called when exporting a value under a specific name,
    fn export_as(&self, _variable_name: &str, _eval: &mut Evaluator<'v, '_>) {
        // Most data types ignore how they are exported
        // but rules/providers like to use it as a helpful hint for users
    }

    /// Set the value at `index` with the new value.
    ///
    /// ```rust
    /// # starlark::assert::is_true(r#"
    /// v = [1, 2, 3]
    /// v[1] = 1
    /// v[2] = [2,3]
    /// v == [1, 1, [2, 3]]
    /// # "#);
    /// ```
    fn set_at(&self, _index: Value<'v>, _new_value: Value<'v>) -> anyhow::Result<()> {
        Err(ValueError::CannotMutateImmutableValue.into())
    }

    /// Set the attribute named `attribute` of the current value to
    /// `value` (e.g. `a.attribute = value`).
    fn set_attr(&self, attribute: &str, _new_value: Value<'v>) -> anyhow::Result<()> {
        ValueError::unsupported(self, &format!(".{}=", attribute))
    }
}

/// Trait implemented by a value stored in arena which delegates
/// it's operations to contained [`StarlarkValue`].
pub(crate) trait StarlarkValueDyn<'v>: 'v {
    // `AValue` is not a `StarlarkValue`, but a `Wrapper` type (or `BlackHole`).
    // `static_type_xxx_of_value` operations return `TypeId` of that `StarlarkValue`,
    // which is not the same of `TypeId` of `AValue` (because `AValue` is a wrapper).
    fn static_type_id_of_value() -> TypeId
    where
        Self: Sized;
    fn static_type_of_value(&self) -> TypeId;

    fn as_debug(&self) -> &dyn Debug;
    /// Get [`StarlarkValue`] as [`AnyLifetime`].
    fn value_as_dyn_any(&self) -> &dyn AnyLifetime<'v>;

    // Remaining operations are identical to operations of `StarlarkValue`.
    // `Wrapper` implementation of these operations delegate to `StarlarkValue`.

    fn get_type(&self) -> &'static str;
    fn get_type_value(&self) -> FrozenStringValue;
    fn matches_type(&self, _ty: &str) -> bool;
    fn get_methods(&self) -> Option<&'static Globals>;
    fn documentation(&self) -> Option<DocItem>;
    fn collect_repr(&self, _collector: &mut String);
    fn to_json(&self) -> anyhow::Result<String>;
    fn to_bool(&self) -> bool;
    fn to_int(&self) -> anyhow::Result<i32>;
    fn get_hash(&self) -> anyhow::Result<u64>;
    fn extra_memory(&self) -> usize;
    fn equals(&self, _other: Value<'v>) -> anyhow::Result<bool>;
    fn compare(&self, _other: Value<'v>) -> anyhow::Result<Ordering>;
    fn invoke(
        &self,
        _me: Value<'v>,
        _location: Option<Span>,
        _args: Arguments<'v, '_>,
        _eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>>;
    fn at(&self, _index: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn slice(
        &self,
        _start: Option<Value<'v>>,
        _stop: Option<Value<'v>>,
        _stride: Option<Value<'v>>,
        _heap: &'v Heap,
    ) -> anyhow::Result<Value<'v>>;
    fn iterate<'a>(
        &'a self,
        _heap: &'v Heap,
    ) -> anyhow::Result<Box<dyn Iterator<Item = Value<'v>> + 'a>>
    where
        'v: 'a;
    fn with_iterator(
        &self,
        _heap: &'v Heap,
        _f: &mut dyn FnMut(&mut dyn Iterator<Item = Value<'v>>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()>;
    fn length(&self) -> anyhow::Result<i32>;
    fn get_attr(&self, _attribute: &str, _heap: &'v Heap) -> Option<Value<'v>>;
    fn has_attr(&self, _attribute: &str) -> bool;
    fn dir_attr(&self) -> Vec<String>;
    fn is_in(&self, _other: Value<'v>) -> anyhow::Result<bool>;
    fn plus(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn minus(&self, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn radd(&self, _lhs: Value<'v>, _heap: &'v Heap) -> Option<anyhow::Result<Value<'v>>>;
    fn add(&self, _rhs: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn sub(&self, _other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn mul(&self, _other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn percent(&self, _other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn floor_div(&self, _other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>>;
    fn bit_and(&self, _other: Value<'v>) -> anyhow::Result<Value<'v>>;
    fn bit_or(&self, _other: Value<'v>) -> anyhow::Result<Value<'v>>;
    fn bit_xor(&self, _other: Value<'v>) -> anyhow::Result<Value<'v>>;
    fn left_shift(&self, _other: Value<'v>) -> anyhow::Result<Value<'v>>;
    fn right_shift(&self, _other: Value<'v>) -> anyhow::Result<Value<'v>>;
    fn export_as(&self, _variable_name: &str, _eval: &mut Evaluator<'v, '_>);
    fn set_at(&self, _index: Value<'v>, _new_value: Value<'v>) -> anyhow::Result<()>;
    fn set_attr(&self, _attribute: &str, _new_value: Value<'v>) -> anyhow::Result<()>;
}
