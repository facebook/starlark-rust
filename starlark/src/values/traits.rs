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

//! The values module define a trait `TypedValue` that defines the attribute of
//! any value in Starlark and a few macro to help implementing this trait.
//! The `Value` struct defines the actual structure holding a TypedValue. It is
//! mostly used to enable mutable and Rc behavior over a TypedValue.
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
    environment::Globals,
    values::{
        function::FunctionInvoker, unsupported, unsupported_owned, unsupported_with,
        ConstFrozenValue, Freezer, Heap, TypedIterable, Value, ValueError, Walker,
    },
};
use gazebo::any::AnyLifetime;
use std::{
    cmp::Ordering,
    fmt::{Debug, Write},
};

pub trait AsTypedValue<'v> {
    fn as_type_name(&self) -> &'static str;
    fn as_typed_value(&self) -> &dyn TypedValue<'v>;
    fn as_dyn_any(&self) -> &dyn AnyLifetime<'v>;
    fn as_dyn_any_mut(&mut self) -> &mut dyn AnyLifetime<'v>;
    fn as_debug(&self) -> &dyn Debug;
}

impl<'v, T: TypedValue<'v> + AnyLifetime<'v>> AsTypedValue<'v> for T {
    fn as_type_name(&self) -> &'static str {
        std::any::type_name::<T>()
    }

    fn as_typed_value(&self) -> &dyn TypedValue<'v> {
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
}

pub trait MutableValue<'v>: TypedValue<'v> {
    fn freeze<'fv>(self: Box<Self>, freezer: &'fv Freezer) -> Box<dyn ImmutableValue<'fv> + 'fv>;

    /// Called by the garbage collection, and must walk over every contained `Value` in the type.
    /// Marked `unsafe` because if you miss a nested `Value`, it will probably segfault.
    unsafe fn walk(&mut self, walker: &Walker<'v>);

    // Called when exporting a value under a specific name,
    // only applies to things that are naturally_mutable().
    // The naturally_mutable constraint occurs because other variables
    // aren't stored in a RefCell, and thus can't be
    // easily/safely converted to a &mut as this function requires.
    fn export_as(&mut self, _heap: &'v Heap, _variable_name: &str) {
        // Most data types ignore how they are exported
        // but rules/providers like to use it as a helpful hint for users
    }
}

pub trait ImmutableValue<'v>: TypedValue<'v> + Send + Sync {
    // This is used when a thaw-on-write value becomes mutable.
    // Requires an expensive shallow-copy in most cases (with a thaw-on-write for
    // the children). Only called for things that are naturally_mutable.
    fn thaw(&self, _heap: &'v Heap) -> Box<dyn MutableValue<'v> + 'v> {
        assert!(!self.naturally_mutable());
        unimplemented!()
    }
}

/// A trait for a value with a type that all variable container
/// will implement.
pub trait TypedValue<'v>: 'v + AsTypedValue<'v> + Debug {
    /// Return a string describing the type of self, as returned by the type()
    /// function.
    fn get_type(&self) -> &'static str;

    /// Like get_type, but returns a reusable Value pointer to it.
    fn get_type_value(&self) -> &'static ConstFrozenValue;

    /// Is this a function type. Function types behave in two specific ways:
    ///
    /// `a.b(c)` is treated as `b(a, c)` and more generally `a.b` is treated
    /// as `b(a, ...)` - even if there are no arguments immediately following.
    ///
    /// The equality/hash of a function is based on its identity - namely
    /// its address in memory.
    fn is_function(&self) -> bool {
        false
    }

    /// Is this value a match for a named type. Usually returns `true` for
    /// values matching `get_type`, but might also work for subtypes it implements.
    fn matches_type(&self, ty: &str) -> bool {
        self.get_type() == ty
    }

    fn get_members(&self) -> Option<&'static Globals> {
        None
    }

    fn naturally_mutable(&self) -> bool {
        false
    }

    // Do not implement this function, it's just syntax sugar over collect_repr
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

    fn to_json(&self) -> String {
        panic!("unsupported for type {}", self.get_type())
    }

    /// Convert self to a Boolean truth value, as returned by the bool()
    /// function.
    fn to_bool(&self) -> bool {
        // Return `true` by default, because this is default when implementing
        // custom types in Python: https://docs.python.org/release/2.5.2/lib/truth.html
        true
    }

    /// Convert self to a integer value, as returned by the int() function if
    /// the type is numeric (not for string).
    /// Works for int and bool (0 = false, 1 = true).
    fn to_int(&self) -> anyhow::Result<i32> {
        unsupported(self, "int()")
    }

    /// Return a hash code for self to be used when self is placed as a key in a Dict.
    /// OperationNotSupported if there is no hash for this value (e.g. list).
    /// Must be stable between frozen and non-frozen values.
    fn get_hash(&self) -> anyhow::Result<u64> {
        if self.is_function() {
            // The Starlark spec says functions must be hashable.
            // We could return the address of the function, but that changes
            // with frozen/non-frozen which breaks freeze for Dict.
            // We could create an atomic counter and use that, but it takes memory,
            // effort, complexity etc, and we don't expect many Dict's keyed by
            // function. Returning 0 as the hash is valid, as Eq will sort it out.
            Ok(0)
        } else {
            Err(ValueError::NotHashableValue(self.get_type().to_owned()).into())
        }
    }

    /// Compare `self` with `other` for equality.
    /// Should only return an error on excessive recursion.
    fn equals(&self, _other: Value<'v>) -> anyhow::Result<bool> {
        // Type is only equal via a pointer
        Ok(false)
    }

    /// Compare `self` with `other`.
    /// This method returns a result of type [`Ordering`].
    ///
    /// Default implementation returns error.
    fn compare(&self, other: Value<'v>) -> anyhow::Result<Ordering> {
        unsupported_with(self, "compare", other)
    }

    /// Perform a call on the object, only meaningfull for function object.
    ///
    /// For instance, if this object is a callable (i.e. a function or a method)
    /// that adds 2 integers then `self.call(vec![Value::new(1),
    /// Value::new(2)], HashMap::new(), None, None)` would return
    /// `Ok(Value::new(3))`.
    ///
    /// # Parameters
    ///
    /// * call_stack: the calling stack, to detect recursion
    /// * type_values: environment used to resolve type fields.
    /// * positional: the list of arguments passed positionally.
    /// * named: the list of argument that were named.
    /// * args: if provided, the `*args` argument.
    /// * kwargs: if provided, the `**kwargs` argument.
    fn new_invoker<'a>(
        &self,
        _me: Value<'v>,
        _heap: &'v Heap,
    ) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        unsupported(self, "call()")
    }

    /// Perform an array or dictionary indirection.
    ///
    /// This returns the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, "[]", index)
    }

    /// Set the value at `index` with `alloc_value`.
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue`
    /// if the value was frozen (but with
    /// `ValueError::OperationNotSupported` if the operation is not supported
    /// on this value, even if the value is immutable, e.g. for numbers).
    ///
    /// ```rust
    /// # starlark::assert::is_true(r#"
    /// v = [1, 2, 3]
    /// v[1] = 1
    /// v[2] = [2,3]
    /// v == [1, 1, [2, 3]]
    /// # "#);
    /// ```
    fn set_at(&mut self, index: Value<'v>, _new_value: Value<'v>) -> anyhow::Result<()> {
        unsupported_with(self, "[]=", index)
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
        unsupported(self, "[::]")
    }

    /// Returns an iterable over the value of this container if this value hold
    /// an iterable container.
    fn iterate(&self) -> anyhow::Result<&(dyn TypedIterable<'v> + 'v)> {
        unsupported(self, "(iter)")
    }

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> anyhow::Result<i32> {
        unsupported(self, "len()")
    }

    /// Get an attribute for the current value as would be returned by dotted
    /// expression (i.e. `a.attribute`).
    ///
    /// __Note__: this does not handle native methods which are handled through
    /// universe.
    fn get_attr(&self, attribute: &str, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        unsupported(self, &format!(".{}", attribute))
    }

    /// Return true if an attribute of name `attribute` exists for the current
    /// value.
    ///
    /// __Note__: this does not handle native methods which are handled through
    /// universe.
    fn has_attr(&self, _attribute: &str) -> bool {
        false
    }

    /// Set the attribute named `attribute` of the current value to
    /// `alloc_value` (e.g. `a.attribute = alloc_value`).
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue`
    /// if the value was frozen or the attribute is immutable (but with
    /// `ValueError::OperationNotSupported` if the operation is not
    /// supported on this value, even if the self is immutable,
    /// e.g. for numbers).
    fn set_attr(&mut self, attribute: &str, _new_value: Value<'v>) -> anyhow::Result<()> {
        unsupported(self, &format!(".{}=", attribute))
    }

    /// Return a vector of string listing all attribute of the current value,
    /// excluding native methods.
    fn dir_attr(&self) -> Vec<String> {
        Vec::new()
    }

    /// Tell wether `other` is in the current value, if it is a container.
    ///
    /// Non container value should return an error
    /// `ValueError::OperationNotSupported`.
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
        unsupported_owned(other.get_type(), "in", Some(self.get_type()))
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
        unsupported(self, "+")
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
        unsupported(self, "-")
    }

    /// Add with the arguments the other way around. Should return None
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
        unsupported_with(self, "+", rhs)
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
        unsupported_with(self, "-", other)
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
        unsupported_with(self, "*", other)
    }

    /// Apply the percent operator between the current value and `other`. Usually used on
    /// strings, as per [the Starlark spec]
    /// (https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#string-interpolation).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # starlark::assert::all_true(r#"
    /// 5 % 3 == 2
    /// "a %s c" % 3 == "a 3 c"
    /// "Hello %s, your score is %d" % ("Bob", 75) == "Hello Bob, your score is 75"
    /// "%d %o %x %c" % (65, 65, 65, 65) == "65 101 41 A"
    /// "%(greeting)s, %(audience)s" % {"greeting": "Hello", "audience": "world"} == "Hello, world"
    /// "Hello %s, welcome" % "Bob" == "Hello Bob, welcome"
    /// "%s%(a)%" % {"a": 1} == "{\"a\": 1}%" # Copy Python corner-cases
    /// "%s%(a)s" % {"a": 1} == "{\"a\": 1}1" # Copy Python corner-cases
    /// "%s" % (1,) == "1"
    /// "%s" % ((1,),) == "(1,)"
    /// "%s" % [1] == "[1]"
    /// "test" % () == "test"
    /// # "#);
    /// ```
    fn percent(&self, other: Value<'v>, _heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, "%", other)
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
        unsupported_with(self, "//", other)
    }

    fn bit_and(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, "&", other)
    }

    fn bit_or(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, "|", other)
    }

    fn bit_xor(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, "^", other)
    }

    fn left_shift(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, "<<", other)
    }

    fn right_shift(&self, other: Value<'v>) -> anyhow::Result<Value<'v>> {
        unsupported_with(self, ">>", other)
    }
}
