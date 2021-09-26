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

use crate::{collections::BorrowHashed, values::StringValue};
/// Deal with all aspects of runtime parameter evaluation.
/// First build a Parameters structure, then use collect to collect the
/// parameters into slots.
use crate::{
    collections::{
        symbol_map::{Symbol, SymbolMap},
        Hashed, SmallMap,
    },
    values::{
        dict::Dict, tuple::Tuple, Freezer, FrozenValue, Heap, Trace, Tracer, UnpackValue, Value,
        ValueError, ValueLike,
    },
};
use either::Either;
use gazebo::{
    cell::ARef,
    coerce::{coerce, Coerce},
    prelude::*,
};
use itertools::Itertools;
use std::{cell::Cell, cmp, convert::TryInto, intrinsics::unlikely, iter};
use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub(crate) enum FunctionError {
    #[error("Missing parameter `{name}` for call to {function}")]
    MissingParameter { name: String, function: String },
    #[error("Found {count} extra positional parameter(s) for call to {function}")]
    ExtraPositionalParameters { count: usize, function: String },
    #[error("Found {} extra named parameter(s) for call to {function}", .names.join(" "))]
    ExtraNamedParameters {
        names: Vec<String>,
        function: String,
    },
    #[error("Parameter `{name}` occurs both explicitly and in **kwargs")]
    RepeatedParameter { name: String },
    #[error("The argument provided for *args is not an identifier")]
    ArgsValueIsNotString,
    #[error("The argument provided for *args is not iterable")]
    ArgsArrayIsNotIterable,
    #[error("The argument provided for **kwargs is not a dictionary")]
    KwArgsIsNotDict,
    #[error("Wrong number of positional parameters, expected between {0} and {0}, got {1}")]
    WrongNumberOfParameters(usize, usize, usize),
}

#[derive(Debug, Clone, Coerce, PartialEq)]
#[repr(C)]
pub(crate) enum ParameterKind<V> {
    Required,
    Optional,
    Defaulted(V),
    Args,
    KWargs,
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for ParameterKind<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        match self {
            Self::Defaulted(v) => v.trace(tracer),
            _ => {}
        }
    }
}

impl<'v> ParameterKind<Value<'v>> {
    fn freeze(&self, freezer: &Freezer) -> anyhow::Result<ParameterKind<FrozenValue>> {
        Ok(match self {
            Self::Defaulted(v) => ParameterKind::Defaulted(v.freeze(freezer)?),
            Self::Required => ParameterKind::Required,
            Self::Optional => ParameterKind::Optional,
            Self::Args => ParameterKind::Args,
            Self::KWargs => ParameterKind::KWargs,
        })
    }
}

/// Define a list of parameters. This code assumes that all names are distinct and that
/// `*args`/`**kwargs` occur in well-formed locations.
// V = Value, or FrozenValue
#[derive(Debug, Clone)]
#[repr(C)]
pub struct ParametersSpec<V> {
    /// Only used in error messages
    function_name: String,

    /// These two fields describe everything about the signature.
    /// The `kinds` lists all the arguments in the order they occur.
    /// The `names` gives a mapping from name to index where the argument lives.
    /// The only entries in `kinds` which are not in `names` are Args/KWargs,
    /// and the iteration order of `names` is the same order as `types`.
    kinds: Vec<ParameterKind<V>>,
    names: SymbolMap<usize>,

    /// Number of arguments that can be filled positionally.
    /// Excludes *args/**kwargs, keyword arguments after *args
    positional: usize,

    /// Has the no_args been passed
    no_args: bool,
    /// The index at which *args should go
    args: Option<usize>,
    /// The index at which **kwargs should go
    kwargs: Option<usize>,
}

// Can't derive this since we don't want ParameterKind to be public
unsafe impl<From: Coerce<To>, To> Coerce<ParametersSpec<To>> for ParametersSpec<From> {}

impl<V> ParametersSpec<V> {
    /// Create a new [`ParametersSpec`] with the given function name.
    pub fn new(function_name: String) -> Self {
        Self::with_capacity(function_name, 0)
    }

    /// Create a new [`ParametersSpec`] with the given function name and an advance capacity hint.
    pub fn with_capacity(function_name: String, capacity: usize) -> Self {
        Self {
            function_name,
            kinds: Vec::with_capacity(capacity),
            names: SymbolMap::with_capacity(capacity),
            positional: 0,
            no_args: false,
            args: None,
            kwargs: None,
        }
    }

    /// Change the function name.
    pub fn set_function_name(&mut self, name: String) {
        self.function_name = name
    }

    fn add(&mut self, name: &str, val: ParameterKind<V>) {
        let i = self.kinds.len();
        self.kinds.push(val);
        let old = self.names.insert(name, i);
        if self.args.is_none() && !self.no_args {
            // If you've already seen `args` or `no_args`, you can't enter these
            // positionally
            self.positional = i + 1;
        }
        assert!(old.is_none());
    }

    /// Add a required parameter. Will be an error if the caller doesn't supply
    /// it. If you want to supply a position-only argument, prepend a `$` to
    /// the name.
    pub fn required(&mut self, name: &str) {
        self.add(name, ParameterKind::Required);
    }

    /// Add an optional parameter. Will be None if the caller doesn't supply it.
    /// If you want to supply a position-only argument, prepend a `$` to the
    /// name.
    pub fn optional(&mut self, name: &str) {
        self.add(name, ParameterKind::Optional);
    }

    /// Add an optional parameter. Will be the default value if the caller
    /// doesn't supply it. If you want to supply a position-only argument,
    /// prepend a `$` to the name.
    pub fn defaulted(&mut self, name: &str, val: V) {
        self.add(name, ParameterKind::Defaulted(val));
    }

    /// Add an `*args` parameter which will be an iterable sequence of parameters,
    /// recorded into a [`Vec`]. A function can only have one `args`
    /// parameter. After this call, any subsequent [`required`](ParametersSpec::required),
    /// [`optional`](ParametersSpec::optional) or [`defaulted`](ParametersSpec::defaulted)
    /// parameters can _only_ be supplied by name.
    pub fn args(&mut self) {
        assert!(self.args.is_none() && !self.no_args);
        self.kinds.push(ParameterKind::Args);
        self.args = Some(self.kinds.len() - 1);
    }

    /// This function has no `*args` parameter, corresponds to the Python parameter `*`.
    /// After this call, any subsequent [`required`](ParametersSpec::required),
    /// [`optional`](ParametersSpec::optional) or [`defaulted`](ParametersSpec::defaulted)
    /// parameters can _only_ be supplied by name.
    pub fn no_args(&mut self) {
        assert!(self.args.is_none() && !self.no_args);
        self.no_args = true;
    }

    /// Add a `**kwargs` parameter which will be a dictionary, recorded into a [`SmallMap`].
    /// A function can only have one `kwargs` parameter.
    /// parameter. After this call, any subsequent [`required`](ParametersSpec::required),
    /// [`optional`](ParametersSpec::optional) or [`defaulted`](ParametersSpec::defaulted)
    /// parameters can _only_ be supplied by position.
    pub fn kwargs(&mut self) {
        assert!(self.kwargs.is_none());
        self.kinds.push(ParameterKind::KWargs);
        self.kwargs = Some(self.kinds.len() - 1);
    }

    /// Produce an approximate signature for the function, combining the name and arguments.
    pub fn signature(&self) -> String {
        let mut collector = String::new();
        self.collect_repr(&mut collector);
        collector
    }

    /// Figure out the argument name at an index in kinds.
    /// Only called in the error path, so is not optimised.
    pub(crate) fn param_name_at(&self, index: usize) -> String {
        match self.kinds[index] {
            ParameterKind::Args => return "args".to_owned(),
            ParameterKind::KWargs => return "kwargs".to_owned(),
            _ => {}
        }
        self.names
            .iter()
            .find(|x| x.1 == index)
            .unwrap()
            .0
            .as_str()
            .to_owned()
    }

    // Generate a good error message for it
    pub(crate) fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.function_name);

        // We used to make the "name" of a function include all its parameters, but that is a lot of
        // details and visually crowds out everything else. Try disabling, although we might want it
        // in some contexts, so don't delete it.
        if false {
            collector.push('(');

            let mut names = self.names.keys();
            let mut next_name = || {
                // We prepend '$' on the front of variable names that are positional-only
                // arguments to the native functions. We rip those off when
                // displaying the signature.
                // The `unwrap` is safe because we must have a names entry for each
                // non-Args/KWargs kind.
                names.next().unwrap().as_str().trim_start_match('$')
            };

            for (i, typ) in self.kinds.iter().enumerate() {
                if i != 0 {
                    collector.push_str(", ");
                }
                match typ {
                    ParameterKind::Required => collector.push_str(next_name()),
                    ParameterKind::Optional | ParameterKind::Defaulted(_) => {
                        collector.push_str(next_name());
                        collector.push_str(" = ...");
                    }
                    ParameterKind::Args => collector.push_str("*args"),
                    ParameterKind::KWargs => collector.push_str("**kwargs"),
                }
            }
            collector.push(')');
        }
    }

    /// Get the index where a user would have supplied "*" as a parameter.
    pub(crate) fn no_args_param_index(&self) -> Option<usize> {
        if self.positional < self.kinds.len() {
            match self.kinds.get(self.positional) {
                Some(ParameterKind::Args) | Some(ParameterKind::KWargs) => None,
                _ => Some(self.positional),
            }
        } else {
            None
        }
    }

    /// Iterate over the parameters
    ///
    /// Returns an iterator over (parameter index, name, kind)
    pub(crate) fn iter_params(&self) -> impl Iterator<Item = (usize, &str, &ParameterKind<V>)> {
        let names: Vec<&str> = self
            .names
            .iter()
            .sorted_by_key(|(_, i)| i)
            .map(|(s, _)| s.as_str())
            .collect();

        self.kinds.iter().enumerate().map(move |(i, kind)| {
            let name = match kind {
                ParameterKind::Args => "*args",
                ParameterKind::KWargs => "**kwargs",
                _ => names
                    .get(i)
                    .map(|s| s.trim_start_match('$'))
                    .expect("name in mapping"),
            };
            (i, name, kind)
        })
    }
}

impl<'v, V: ValueLike<'v>> ParametersSpec<V> {
    pub fn len(&self) -> usize {
        self.kinds.len()
    }

    /// Move parameters from [`Arguments`] to a list of [`Value`],
    /// using the supplied [`ParametersSpec`].
    pub fn collect(
        &self,
        args: Arguments<'v, '_>,
        slots: &[Cell<Option<Value<'v>>>],
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        self.collect_inline(args, slots, heap)
    }

    pub fn collect_into<const N: usize>(
        &self,
        args: Arguments<'v, '_>,
        heap: &'v Heap,
    ) -> anyhow::Result<[Cell<Option<Value<'v>>>; N]> {
        let slots = [(); N].map(|_| Cell::new(None));
        self.collect(args, &slots, heap)?;
        Ok(slots)
    }

    /// A variant of collect that is always inlined
    /// for Def and NativeFunction that are hot-spots
    #[inline(always)]
    pub(crate) fn collect_inline(
        &self,
        args: Arguments<'v, '_>,
        slots: &[Cell<Option<Value<'v>>>],
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        // If the arguments equal the length and the kinds, and we don't have any other args,
        // then no_args, *args and **kwargs must all be unset,
        // and we don't have to crate args/kwargs objects, we can skip everything else
        if args.pos.len() == self.positional
            && args.pos.len() == self.kinds.len()
            && args.named.is_empty()
            && args.args.is_none()
            && args.kwargs.is_none()
        {
            for (v, s) in args.pos.iter().zip(slots.iter()) {
                s.set(Some(*v));
            }

            return Ok(());
        }

        self.collect_slow(args, slots, heap)
    }

    fn collect_slow(
        &self,
        args: Arguments<'v, '_>,
        slots: &[Cell<Option<Value<'v>>>],
        heap: &'v Heap,
    ) -> anyhow::Result<()> {
        // Return true if the value is a duplicate
        #[inline(always)]
        fn add_kwargs<'v>(
            kwargs: &mut Option<Box<SmallMap<StringValue<'v>, Value<'v>>>>,
            key: Hashed<StringValue<'v>>,
            val: Value<'v>,
        ) -> bool {
            match kwargs {
                None => {
                    let mut mp = SmallMap::with_capacity_largest_vec();
                    mp.insert_hashed(key, val);
                    *kwargs = Some(box mp);
                    false
                }
                Some(mp) => mp.insert_hashed(key, val).is_some(),
            }
        }

        let len = self.kinds.len();
        // We might do unchecked stuff later on, so make sure we have as many slots as we expect
        assert!(slots.len() >= len);

        let mut star_args = Vec::new();
        let mut kwargs = None;
        let mut next_position = 0;

        // First deal with positional parameters
        if args.pos.len() <= self.positional {
            // fast path for when we don't need to bounce down to filling in args
            for (v, s) in args.pos.iter().zip(slots.iter()) {
                s.set(Some(*v));
            }
            next_position = args.pos.len();
        } else {
            for v in args.pos {
                if next_position < self.positional {
                    slots[next_position].set(Some(*v));
                    next_position += 1;
                } else {
                    star_args.push(*v);
                }
            }
        }

        // Next deal with named parameters
        // The lowest position at which we've written a name.
        // If at the end lowest_name is less than next_position, we got the same variable twice.
        // So no duplicate checking until after all positional arguments
        let mut lowest_name = usize::MAX;
        // Avoid a lot of loop setup etc in the common case
        if !args.names.is_empty() {
            for ((name, name_value), v) in args.names.iter().zip(args.named) {
                // Safe to use new_unchecked because hash for the Value and str are the same
                match self.names.get(name) {
                    None => {
                        add_kwargs(
                            &mut kwargs,
                            Hashed::new_unchecked(name.small_hash(), *name_value),
                            *v,
                        );
                    }
                    Some(i) => {
                        slots[*i].set(Some(*v));
                        lowest_name = cmp::min(lowest_name, *i);
                    }
                }
            }
        }

        // Next up are the *args parameters
        if let Some(param_args) = args.args {
            param_args
                .with_iterator(heap, |it| {
                    for v in it {
                        if next_position < self.positional {
                            slots[next_position].set(Some(v));
                            next_position += 1;
                        } else {
                            star_args.push(v);
                        }
                    }
                })
                .map_err(|_| FunctionError::ArgsArrayIsNotIterable)?;
        }

        // Check if the named arguments clashed with the positional arguments
        if unlikely(next_position > lowest_name) {
            return Err(FunctionError::RepeatedParameter {
                name: self.param_name_at(lowest_name),
            }
            .into());
        }

        // Now insert the kwargs, if there are any
        if let Some(param_kwargs) = args.kwargs {
            match Dict::from_value(param_kwargs) {
                Some(y) => {
                    for (k, v) in y.iter_hashed() {
                        match StringValue::new(*k.key()) {
                            None => return Err(FunctionError::ArgsValueIsNotString.into()),
                            Some(s) => {
                                let repeat = match self.names.get_hashed_str(
                                    BorrowHashed::new_unchecked(k.hash(), s.as_str()),
                                ) {
                                    None => add_kwargs(
                                        &mut kwargs,
                                        Hashed::new_unchecked(k.hash(), s),
                                        v,
                                    ),
                                    Some(i) => {
                                        let this_slot = &slots[*i];
                                        let repeat = this_slot.get().is_some();
                                        this_slot.set(Some(v));
                                        repeat
                                    }
                                };
                                if unlikely(repeat) {
                                    return Err(FunctionError::RepeatedParameter {
                                        name: s.as_str().to_owned(),
                                    }
                                    .into());
                                }
                            }
                        }
                    }
                }
                None => return Err(FunctionError::KwArgsIsNotDict.into()),
            }
        }

        // We have moved parameters into all the relevant slots, so need to finalise things.
        // We need to set default values and error if any required values are missing
        let kinds = &self.kinds;
        // This code is very hot, and setting up iterators was a noticeable bottleneck.
        for index in next_position..kinds.len() {
            // The number of locals must be at least the number of parameters, see `collect`
            // which reserves `max(_, kinds.len())`.
            let slot = unsafe { slots.get_unchecked(index) };
            let def = unsafe { kinds.get_unchecked(index) };

            // We know that up to next_position got filled positionally, so we don't need to check those
            if slot.get().is_some() {
                continue;
            }
            match def {
                ParameterKind::Required => {
                    return Err(FunctionError::MissingParameter {
                        name: self.param_name_at(index),
                        function: self.signature(),
                    }
                    .into());
                }
                ParameterKind::Defaulted(x) => {
                    slot.set(Some(x.to_value()));
                }
                _ => {}
            }
        }

        // Now set the kwargs/args slots, if they are requested, and fail it they are absent but used
        // Note that we deliberately give warnings about missing parameters _before_ giving warnings
        // about unexpected extra parameters, so if a user mis-spells an argument they get a better error.
        if let Some(args_pos) = self.args {
            slots[args_pos].set(Some(heap.alloc(Tuple::new(star_args))));
        } else if unlikely(!star_args.is_empty()) {
            return Err(FunctionError::ExtraPositionalParameters {
                count: star_args.len(),
                function: self.signature(),
            }
            .into());
        }

        if let Some(kwargs_pos) = self.kwargs {
            let kwargs = match kwargs.take() {
                Some(kwargs) => Dict::new(coerce(*kwargs)),
                None => Dict::default(),
            };
            slots[kwargs_pos].set(Some(heap.alloc(kwargs)));
        } else if let Some(kwargs) = kwargs {
            return Err(FunctionError::ExtraNamedParameters {
                names: kwargs.keys().map(|x| x.as_str().to_owned()).collect(),
                function: self.signature(),
            }
            .into());
        }
        Ok(())
    }
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for ParametersSpec<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.kinds.trace(tracer);
    }
}

impl<'v> ParametersSpec<Value<'v>> {
    /// Used to freeze a [`ParametersSpec`].
    pub fn freeze(self, freezer: &Freezer) -> anyhow::Result<ParametersSpec<FrozenValue>> {
        Ok(ParametersSpec {
            function_name: self.function_name,
            kinds: self.kinds.try_map(|v| v.freeze(freezer))?,
            names: self.names,
            positional: self.positional,
            no_args: self.no_args,
            args: self.args,
            kwargs: self.kwargs,
        })
    }
}

/// Parse a series of parameters which were specified by [`ParametersSpec`].
pub struct ParametersParser<'v, 'a>(std::slice::Iter<'a, Cell<Option<Value<'v>>>>);

impl<'v, 'a> ParametersParser<'v, 'a> {
    pub fn new(slots: &'a [Cell<Option<Value<'v>>>]) -> Self {
        Self(slots.iter())
    }

    // Utility for improving the error message with more information
    fn named_err<T>(name: &str, x: Option<T>) -> anyhow::Result<T> {
        x.ok_or_else(|| ValueError::IncorrectParameterTypeNamed(name.to_owned()).into())
    }

    fn get_next(&mut self) -> Option<Value<'v>> {
        let v = self
            .0
            .next()
            .expect("ParametersParser: wrong number of requested arguments");
        v.get()
    }

    pub fn this<T: UnpackValue<'v>>(&self, this: Option<Value<'v>>) -> anyhow::Result<T> {
        Self::named_err("this", this.and_then(T::unpack_value))
    }

    /// Obtain the next parameter, corresponding to [`ParametersSpec::optional`].
    /// It is an error to request more parameters than were specified.
    /// The `name` is only used for error messages.
    pub fn next_opt<T: UnpackValue<'v>>(&mut self, name: &str) -> anyhow::Result<Option<T>> {
        match self.get_next() {
            None => Ok(None),
            Some(v) => Ok(Some(Self::named_err(name, T::unpack_value(v))?)),
        }
    }

    /// Obtain the next parameter, which can't be defined by [`ParametersSpec::optional`].
    /// It is an error to request more parameters than were specified.
    /// The `name` is only used for error messages.
    pub fn next<T: UnpackValue<'v>>(&mut self, name: &str) -> anyhow::Result<T> {
        // After ParametersCollect.done() all variables will be Some,
        // apart from those where we called ParametersSpec.optional(),
        // and for those we chould call next_opt()

        // This is definitely not unassigned because ParametersCollect.done checked
        // that.
        let v = self.get_next().unwrap();
        Self::named_err(name, T::unpack_value(v))
    }
}

#[derive(Default, Clone, Copy, Dupe)]
pub struct Arguments<'v, 'a> {
    /// This argument, used in method calls.
    pub this: Option<Value<'v>>,
    /// Positional arguments.
    pub pos: &'a [Value<'v>],
    /// Named arguments.
    pub named: &'a [Value<'v>],
    /// Names of named arguments.
    ///
    /// `named` length must be equal to `names` length.
    pub names: &'a [(Symbol, StringValue<'v>)],
    /// `*args` argument.
    pub args: Option<Value<'v>>,
    /// `**kwargs` argument.
    pub kwargs: Option<Value<'v>>,
}

impl<'v, 'a> Arguments<'v, 'a> {
    /// Unwrap all named arguments (both explicit and in `**kwargs`) into a dictionary.
    ///
    /// This operation fails if named argument names are not unique.
    pub fn names(&self) -> anyhow::Result<Dict<'v>> {
        match self.unpack_kwargs()? {
            None => {
                let mut result = SmallMap::with_capacity(self.names.len());
                for (k, v) in self.names.iter().zip(self.named) {
                    result
                        .insert_hashed(Hashed::new_unchecked(k.0.small_hash(), k.1.to_value()), *v);
                }
                Ok(Dict::new(result))
            }
            Some(kwargs) => {
                if self.names.is_empty() {
                    for k in kwargs.content.keys() {
                        Arguments::unpack_kwargs_key(*k)?;
                    }
                    Ok(kwargs.clone())
                } else {
                    // We have to insert the names before the kwargs since the iteration order is observable
                    let mut result =
                        SmallMap::with_capacity(self.names.len() + kwargs.content.len());
                    for (k, v) in self.names.iter().zip(self.named) {
                        result.insert_hashed(
                            Hashed::new_unchecked(k.0.small_hash(), k.1.to_value()),
                            *v,
                        );
                    }
                    for (k, v) in kwargs.iter_hashed() {
                        let s = Arguments::unpack_kwargs_key(*k.key())?;
                        let old = result.insert_hashed(k, v);
                        if unlikely(old.is_some()) {
                            return Err(
                                FunctionError::RepeatedParameter { name: s.to_owned() }.into()
                            );
                        }
                    }
                    Ok(Dict::new(result))
                }
            }
        }
    }

    /// Unpack all positional parameters into an iterator.
    pub fn positions<'b>(
        &'b self,
        heap: &'v Heap,
    ) -> anyhow::Result<impl Iterator<Item = Value<'v>> + 'b> {
        let tail = match self.args {
            None => Either::Left(iter::empty()),
            Some(args) => Either::Right(args.iterate(heap)?),
        };
        Ok(self.pos.iter().copied().chain(tail))
    }

    /// Examine the `kwargs` field, converting it to a [`Dict`] or failing.
    /// Note that even if this operation succeeds, the keys in the kwargs
    /// will _not_ have been validated to be strings (as they must be).
    /// The arguments may also overlap with named, which would be an error.
    #[inline(always)]
    pub fn unpack_kwargs(&self) -> anyhow::Result<Option<ARef<'v, Dict<'v>>>> {
        match self.kwargs {
            None => Ok(None),
            Some(kwargs) => match Dict::from_value(kwargs) {
                None => Err(FunctionError::KwArgsIsNotDict.into()),
                Some(x) => Ok(Some(x)),
            },
        }
    }

    /// Confirm that a key in the `kwargs` field is indeed a string, or [`Err`].
    #[inline(always)]
    pub fn unpack_kwargs_key(k: Value<'v>) -> anyhow::Result<&'v str> {
        match k.unpack_str() {
            None => Err(FunctionError::ArgsValueIsNotString.into()),
            Some(k) => Ok(k),
        }
    }

    /// Produce [`Err`] if there are any positional arguments.
    #[inline(always)]
    pub fn no_positional_args(&self, heap: &'v Heap) -> anyhow::Result<()> {
        let [] = self.positional(heap)?;
        Ok(())
    }

    /// Produce [`Err`] if there are any named (i.e. non-positional) arguments.
    #[inline(always)]
    pub fn no_named_args(&self) -> anyhow::Result<()> {
        #[cold]
        #[inline(never)]
        fn bad(x: &Arguments) -> anyhow::Result<()> {
            // We might have a empty kwargs dictionary, but probably have an error
            let mut extra = Vec::new();
            extra.extend(x.names.iter().map(|x| x.0.as_str().to_owned()));
            if let Some(kwargs) = x.unpack_kwargs()? {
                for k in kwargs.content.keys() {
                    extra.push(Arguments::unpack_kwargs_key(*k)?.to_owned());
                }
            }
            if extra.is_empty() {
                Ok(())
            } else {
                // Would be nice to give a better name here, but it's in the call stack, so no big deal
                Err(FunctionError::ExtraNamedParameters {
                    names: extra,
                    function: "function".to_owned(),
                }
                .into())
            }
        }

        if self.named.is_empty() && self.kwargs.is_none() {
            Ok(())
        } else {
            bad(self)
        }
    }

    /// Collect exactly `N` positional arguments from the [`Arguments`], failing if there are too many/few
    /// arguments. Ignores named arguments.
    #[inline(always)]
    pub fn positional<const N: usize>(&self, heap: &'v Heap) -> anyhow::Result<[Value<'v>; N]> {
        #[cold]
        #[inline(never)]
        fn rare<'v, const N: usize>(
            x: &Arguments<'v, '_>,
            heap: &'v Heap,
        ) -> anyhow::Result<[Value<'v>; N]> {
            // Very sad that we allocate into a vector, but I expect calling into a small positional argument
            // with a *args is very rare.
            let xs = x
                .pos
                .iter()
                .copied()
                .chain(x.args.unwrap().iterate(heap)?)
                .collect::<Vec<_>>();
            xs.as_slice()
                .try_into()
                .map_err(|_| FunctionError::WrongNumberOfParameters(N, N, x.pos.len()).into())
        }

        if self.args.is_none() {
            self.pos
                .try_into()
                .map_err(|_| FunctionError::WrongNumberOfParameters(N, N, self.pos.len()).into())
        } else {
            rare(self, heap)
        }
    }

    /// Collect exactly `REQUIRED` positional arguments, plus at most `OPTIONAL` positional arguments
    /// from the [`Arguments`], failing if there are too many/few arguments. Ignores named arguments.
    /// The `OPTIONAL` array will never have a [`Some`] after a [`None`].
    #[inline(always)]
    pub fn optional<const REQUIRED: usize, const OPTIONAL: usize>(
        &self,
        heap: &'v Heap,
    ) -> anyhow::Result<([Value<'v>; REQUIRED], [Option<Value<'v>>; OPTIONAL])> {
        #[cold]
        #[inline(never)]
        fn rare<'v, const REQUIRED: usize, const OPTIONAL: usize>(
            x: &Arguments<'v, '_>,
            heap: &'v Heap,
        ) -> anyhow::Result<([Value<'v>; REQUIRED], [Option<Value<'v>>; OPTIONAL])> {
            // Very sad that we allocate into a vector, but I expect calling into a small positional argument
            // with a *args is very rare.
            let args = match x.args {
                None => box None.into_iter(),
                Some(args) => args.iterate(heap)?,
            };
            let xs = x.pos.iter().copied().chain(args).collect::<Vec<_>>();
            if xs.len() >= REQUIRED && xs.len() <= REQUIRED + OPTIONAL {
                let required = xs[0..REQUIRED].try_into().unwrap();
                let mut optional = [None; OPTIONAL];
                for (a, b) in optional.iter_mut().zip(&xs[REQUIRED..]) {
                    *a = Some(*b);
                }
                Ok((required, optional))
            } else {
                Err(
                    FunctionError::WrongNumberOfParameters(REQUIRED, REQUIRED + OPTIONAL, xs.len())
                        .into(),
                )
            }
        }

        if self.args.is_none()
            && self.pos.len() >= REQUIRED
            && self.pos.len() <= REQUIRED + OPTIONAL
        {
            let required = self.pos[0..REQUIRED].try_into().unwrap();
            let mut optional = [None; OPTIONAL];
            for (a, b) in optional.iter_mut().zip(&self.pos[REQUIRED..]) {
                *a = Some(*b);
            }
            Ok((required, optional))
        } else {
            rare(self, heap)
        }
    }

    /// Collect 1 positional arguments from the [`Arguments`], failing if there are too many/few
    /// arguments. Ignores named arguments.
    #[inline(always)]
    pub fn positional1(&self, heap: &'v Heap) -> anyhow::Result<Value<'v>> {
        // Could be implemented more directly, let's see if profiling shows it up
        let [x] = self.positional(heap)?;
        Ok(x)
    }

    /// Collect up to 1 optional arguments from the [`Arguments`], failing if there are too many
    /// arguments. Ignores named arguments.
    #[inline(always)]
    pub fn optional1(&self, heap: &'v Heap) -> anyhow::Result<Option<Value<'v>>> {
        // Could be implemented more directly, let's see if profiling shows it up
        let ([], [x]) = self.optional(heap)?;
        Ok(x)
    }
}

// Utility for improving the error message with more information
fn named_err<T>(name: &str, x: Option<T>) -> anyhow::Result<T> {
    x.ok_or_else(|| ValueError::IncorrectParameterTypeNamed(name.to_owned()).into())
}

impl Arguments<'_, '_> {
    /// Utility for checking a `this` parameter matches what you expect.
    pub fn check_this<'v, T: UnpackValue<'v>>(this: Option<Value<'v>>) -> anyhow::Result<T> {
        named_err("this", this.and_then(T::unpack_value))
    }

    /// Utility for checking a required parameter matches what you expect.
    pub fn check_required<'v, T: UnpackValue<'v>>(
        name: &str,
        x: Option<Value<'v>>,
    ) -> anyhow::Result<T> {
        named_err(name, x.and_then(T::unpack_value))
    }

    /// Utility for checking an optional parameter matches what you expect.
    pub fn check_optional<'v, T: UnpackValue<'v>>(
        name: &str,
        x: Option<Value<'v>>,
    ) -> anyhow::Result<Option<T>> {
        match x {
            None => Ok(None),
            Some(x) => named_err(name, T::unpack_value(x).map(Some)),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parameter_unpack() {
        let heap = Heap::new();
        fn f<'v, F: Fn(&Arguments<'v, '_>), const N: usize>(heap: &'v Heap, op: F) {
            for i in 0..=N {
                let mut p = Arguments::default();
                let pos = (0..i).map(|x| Value::new_int(x as i32)).collect::<Vec<_>>();
                let args = (i..N).map(|x| Value::new_int(x as i32)).collect::<Vec<_>>();
                let empty_args = args.is_empty();
                p.pos = &pos;
                p.args = Some(heap.alloc(args));
                op(&p);
                if empty_args {
                    p.args = None;
                    op(&p);
                }
            }
        }

        f::<_, 0>(&heap, |p| {
            assert_eq!(&p.positional::<0>(&heap).unwrap(), &[]);
            assert!(&p.positional::<1>(&heap).is_err());
            assert!(&p.positional::<2>(&heap).is_err());
            assert_eq!(&p.optional::<0, 1>(&heap).unwrap(), &([], [None]));
            assert!(&p.optional::<1, 1>(&heap).is_err());
            assert_eq!(&p.optional::<0, 2>(&heap).unwrap(), &([], [None, None]));
        });
        f::<_, 1>(&heap, |p| {
            assert!(&p.positional::<0>(&heap).is_err());
            assert_eq!(&p.positional::<1>(&heap).unwrap(), &[Value::new_int(0)]);
            assert!(&p.positional::<2>(&heap).is_err());
            assert_eq!(
                &p.optional::<0, 1>(&heap).unwrap(),
                &([], [Some(Value::new_int(0))])
            );
            assert_eq!(
                &p.optional::<1, 1>(&heap).unwrap(),
                &([Value::new_int(0)], [None])
            );
            assert_eq!(
                &p.optional::<0, 2>(&heap).unwrap(),
                &([], [Some(Value::new_int(0)), None])
            );
        });
        f::<_, 2>(&heap, |p| {
            assert!(&p.positional::<0>(&heap).is_err());
            assert!(&p.positional::<1>(&heap).is_err());
            assert_eq!(
                &p.positional::<2>(&heap).unwrap(),
                &[Value::new_int(0), Value::new_int(1)]
            );
            assert!(p.optional::<0, 1>(&heap).is_err());
            assert_eq!(
                &p.optional::<1, 1>(&heap).unwrap(),
                &([Value::new_int(0)], [Some(Value::new_int(1))])
            );
            assert_eq!(
                &p.optional::<0, 2>(&heap).unwrap(),
                &([], [Some(Value::new_int(0)), Some(Value::new_int(1))])
            );
        });
        f::<_, 3>(&heap, |p| {
            assert!(&p.positional::<0>(&heap).is_err());
            assert!(&p.positional::<1>(&heap).is_err());
            assert!(&p.positional::<2>(&heap).is_err());
            assert!(p.optional::<0, 1>(&heap).is_err());
            assert!(p.optional::<1, 1>(&heap).is_err());
            assert!(p.optional::<0, 2>(&heap).is_err());
        });
    }

    #[test]
    fn test_parameter_no_named() {
        let heap = Heap::new();
        let mut p = Arguments::default();
        assert!(p.no_named_args().is_ok());

        // Test lots of forms of kwargs work properly
        p.kwargs = Some(Value::new_none());
        assert!(p.no_named_args().is_err());
        p.kwargs = Some(heap.alloc(Dict::default()));
        assert!(p.no_named_args().is_ok());
        let mut sm = SmallMap::new();
        sm.insert_hashed(heap.alloc_str_hashed("test"), Value::new_none());
        p.kwargs = Some(heap.alloc(Dict::new(sm)));
        assert!(p.no_named_args().is_err());

        // Test named arguments work properly
        p.kwargs = None;
        let named = [Value::new_none()];
        p.named = &named;
        let names = [(Symbol::new("test"), heap.alloc_string_value("test"))];
        p.names = &names;
        assert!(p.no_named_args().is_err());
    }

    #[test]
    fn test_parameter_iteration() {
        let mut p = ParametersSpec::<FrozenValue>::new("f".to_owned());
        p.required("a");
        p.optional("b");
        p.no_args();
        p.optional("c");
        p.kwargs();

        let params: Vec<(usize, &str, &ParameterKind<FrozenValue>)> = p.iter_params().collect();

        let expected: Vec<(usize, &str, &ParameterKind<FrozenValue>)> = vec![
            (0, "a", &ParameterKind::Required),
            (1, "b", &ParameterKind::Optional),
            (2, "c", &ParameterKind::Optional),
            (3, "**kwargs", &ParameterKind::KWargs),
        ];

        assert_eq!(expected, params);
        assert_eq!(Some(2), p.no_args_param_index());

        let mut p = ParametersSpec::<FrozenValue>::new("f".to_owned());
        p.required("a");
        p.args();
        p.kwargs();

        let params: Vec<(usize, &str, &ParameterKind<FrozenValue>)> = p.iter_params().collect();

        let expected: Vec<(usize, &str, &ParameterKind<FrozenValue>)> = vec![
            (0, "a", &ParameterKind::Required),
            (1, "*args", &ParameterKind::Args),
            (2, "**kwargs", &ParameterKind::KWargs),
        ];

        assert_eq!(expected, params);
        assert_eq!(None, p.no_args_param_index());
    }
}
