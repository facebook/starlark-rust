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
    environment::Globals,
    eval::{Evaluator, Parameters},
    values::{
        function::FUNCTION_TYPE, ConstFrozenValue, ControlError, Freezer, Heap, StarlarkIterable,
        Tracer, Value, ValueError,
    },
};
use gazebo::any::AnyLifetime;
use std::{
    cmp::Ordering,
    fmt::{Debug, Write},
};

/// Helper trait used in [`StarlarkValue`] - has a single global implementation.
pub trait AsStarlarkValue<'v> {
    fn as_starlark_value(&self) -> &dyn StarlarkValue<'v>;
    fn as_dyn_any(&self) -> &dyn AnyLifetime<'v>;
    fn as_dyn_any_mut(&mut self) -> &mut dyn AnyLifetime<'v>;
    fn as_debug(&self) -> &dyn Debug;

    fn type_name(&self) -> &'static str;
}

impl<'v, T: StarlarkValue<'v>> AsStarlarkValue<'v> for T {
    fn as_starlark_value(&self) -> &dyn StarlarkValue<'v> {
        self
    }
    fn as_dyn_any(&self) -> &dyn AnyLifetime<'v> {
        self
    }
    fn as_dyn_any_mut(&mut self) -> &mut dyn AnyLifetime<'v> {
        self
    }
    fn as_debug(&self) -> &dyn Debug {
        self
    }

    fn type_name(&self) -> &'static str {
        std::any::type_name::<T>()
    }
}

/// Helper trait used in [`SimpleValue`] - has a single global implementation.
pub trait AsSimpleValue {
    fn as_box_starlark_value(self: Box<Self>) -> Box<dyn StarlarkValue<'static> + Send + Sync>;
}

impl<T: SimpleValue> AsSimpleValue for T {
    fn as_box_starlark_value(self: Box<Self>) -> Box<dyn StarlarkValue<'static> + Send + Sync> {
        self
    }
}

/// Called by the garbage collection, and must walk over every contained `Value` in the type.
/// Marked `unsafe` because if you miss a nested `Value`, it will probably segfault.
pub unsafe trait Trace<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>);
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
/// use starlark::values::{AnyLifetime, ComplexValue, Freezer, FrozenValue, SimpleValue, StarlarkValue, Value, ValueLike, Trace, Tracer};
/// use starlark::{starlark_complex_value, starlark_type};
///
/// #[derive(Debug)]
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
/// unsafe impl<'v> Trace<'v> for One<'v> {
///     fn trace(&mut self, tracer: &Tracer<'v>) {
///         // If there are any `Value`s we don't call `walk` on, its segfault time!
///         tracer.trace(&mut self.0);
///     }
/// }
///
/// impl<'v> ComplexValue<'v> for One<'v> {
///     fn freeze(self: Box<Self>, freezer: &Freezer) -> anyhow::Result<Box<dyn SimpleValue>> {
///         Ok(Box::new(OneGen(self.0.freeze(freezer)?)))
///     }
/// }
/// ```
///
/// The [`starlark_complex_value!`] macro defines two type aliases.
///
/// ```
/// # use crate::starlark::values::*;
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
///
///     // Obtain a mutable reference to `One` from a `Value`,
///     // but only works if the object returns `true` from `is_mutable`.
///     pub fn from_value_mut(x: Value<'v>, heap: &'v Heap) -> anyhow::Result<Option<RefMut<'v, Self>>> {
/// # unimplemented!(
/// # r#"
///         ...
/// # "#);
///     }
/// }
/// ```
///
/// ## Mutable types containing [`Value`]
///
/// If a container is mutable, [`starlark_complex_value!`] still works.
/// To enable mutability return [`true`] from [`is_mutable`](ComplexValue::is_mutable),
/// then the `from_value_mut` function will work.
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
    /// Can this value be mutated using a `&mut self` parameter?
    /// Defaults to [`false`].
    /// The result of this value should be consistent for the duration of the
    /// value's life.
    fn is_mutable(&self) -> bool {
        false
    }

    /// Freeze a value. The frozen value _must_ be equal to the original,
    /// and produce the same hash.
    fn freeze(self: Box<Self>, freezer: &Freezer) -> anyhow::Result<Box<dyn SimpleValue>>;

    /// Called when exporting a value under a specific name,
    /// only applies to things that return [`true`] for [`is_mutable()`](ComplexValue::is_mutable).
    fn export_as(&mut self, _variable_name: &str, _eval: &mut Evaluator<'v, '_>) {
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
    fn set_at(
        &mut self,
        _me: Value<'v>,
        index: Value<'v>,
        _new_value: Value<'v>,
    ) -> anyhow::Result<()> {
        ValueError::unsupported_with(self, "[]=", index)
    }

    /// Set the attribute named `attribute` of the current value to
    /// `value` (e.g. `a.attribute = value`).
    fn set_attr(&mut self, attribute: &str, _new_value: Value<'v>) -> anyhow::Result<()> {
        ValueError::unsupported(self, &format!(".{}=", attribute))
    }
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
pub trait SimpleValue: StarlarkValue<'static> + AsSimpleValue + Send + Sync {}

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
/// [`get_type`](StarlarkValue::get_type) and [`get_type_value`](StarlarkValue::get_type_value).
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
pub trait StarlarkValue<'v>: 'v + AnyLifetime<'v> + AsStarlarkValue<'v> + Debug {
    /// Return a string describing the type of self, as returned by the type()
    /// function.
    fn get_type(&self) -> &'static str;

    /// Like get_type, but returns a reusable Value pointer to it.
    fn get_type_value(&self) -> &'static ConstFrozenValue;

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

    /// Helper to use [`collect_repr`](StarlarkValue::collect_repr),
    /// do not implement it (the default value always works).
    fn to_repr(&self) -> String {
        let mut s = String::new();
        self.collect_repr(&mut s);
        s
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
        _params: Parameters<'v, '_>,
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
    fn iterate(&self) -> anyhow::Result<&(dyn StarlarkIterable<'v> + 'v)> {
        ValueError::unsupported(self, "(iter)")
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
}
