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

/// Deal with all aspects of runtime parameter evaluation.
/// First build a Parameters structure, then use collect to collect the
/// parameters into slots.
use crate::{
    collections::{BorrowHashed, Hashed, SmallMap},
    values::{
        dict::Dict, tuple::Tuple, Freezer, FrozenValue, Heap, UnpackValue, Value, ValueError,
        ValueLike, ValueRef, Walker,
    },
};
use gazebo::{cell::ARef, prelude::*};
use std::{cmp, mem, slice::Iter};
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
    KWArgsIsNotDict,
}

#[derive(Debug, Clone)]
enum ParameterKind<V> {
    Required,
    Optional,
    Defaulted(V),
    Args,
    KWargs,
}

impl<'v> ParameterKind<Value<'v>> {
    fn freeze(&self, freezer: &Freezer) -> ParameterKind<FrozenValue> {
        match self {
            Self::Defaulted(v) => ParameterKind::Defaulted(v.freeze(freezer)),
            Self::Required => ParameterKind::Required,
            Self::Optional => ParameterKind::Optional,
            Self::Args => ParameterKind::Args,
            Self::KWargs => ParameterKind::KWargs,
        }
    }

    fn walk(&mut self, walker: &Walker<'v>) {
        match self {
            Self::Defaulted(v) => walker.walk(v),
            _ => {}
        }
    }
}

/// Define a list of parameters. This code assumes that all names are distinct and that
/// `*args`/`**kwargs` occur in well-formed locations.
#[derive(Debug, Clone)]
// V = Value, or FrozenValue
pub struct ParametersSpec<V> {
    /// Only used in error messages
    function_name: String,

    /// These two fields describe everything about the signature.
    /// The `kinds` lists all the arguments in the order they occur.
    /// The `names` gives a mapping from name to index where the argument lives.
    /// The only entries in `kinds` which are not in `names` are Args/KWargs,
    /// and the iteration order of `names` is the same order as `types`.
    kinds: Vec<ParameterKind<V>>,
    names: SmallMap<String, usize>,

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

impl<V> ParametersSpec<V> {
    /// Create a new [`ParametersSpec`] with the given function name.
    pub fn new(function_name: String) -> Self {
        Self {
            function_name,
            kinds: Vec::new(),
            names: SmallMap::new(),
            positional: 0,
            no_args: false,
            args: None,
            kwargs: None,
        }
    }

    /// Create a new [`ParametersSpec`] with the given function name and an advance capacity hint.
    pub fn with_capacity(function_name: String, capacity: usize) -> Self {
        Self {
            function_name,
            kinds: Vec::with_capacity(capacity),
            names: SmallMap::with_capacity(capacity),
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
        let old = self.names.insert(name.to_owned(), i);
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

    /// Add an optional parameter. Will be the edefault value if the caller
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

    pub(crate) fn collect<'v, 'a>(
        me: ARef<'a, Self>,
        slots: usize,
    ) -> ParametersCollect<'v, 'a, V> {
        let len = me.kinds.len();
        ParametersCollect {
            params: me,
            slots: vec![ValueRef::new_unassigned(); cmp::max(slots, len)],
            only_positional: true,
            next_position: 0,
            args: Vec::new(),
            kwargs: SmallMap::new(),
            err: None,
        }
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
        // We want names[#index], ignoring all the args/kwargs up until this position
        let mut new_index = index;
        for k in self.kinds.iter().take(index) {
            match k {
                ParameterKind::Args | ParameterKind::KWargs => new_index -= 1,
                _ => {}
            }
        }
        self.names.get_index(new_index).unwrap().0.clone()
    }

    // Generate a good error message for it
    pub(crate) fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.function_name);
        collector.push('(');

        let mut names = self.names.keys();
        let mut next_name = || {
            // We prepend '$' on the front of variable names that are positional-only
            // arguments to the native functions. We rip those off when
            // displaying the signature.
            // The `unwrap` is safe because we must have a names entry for each
            // non-Args/KWargs kind.
            names.next().unwrap().trim_start_match('$')
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

impl<'v> ParametersSpec<Value<'v>> {
    /// Used to freeze a [`ParametersSpec`].
    pub fn freeze(self, freezer: &Freezer) -> ParametersSpec<FrozenValue> {
        ParametersSpec {
            function_name: self.function_name,
            kinds: self.kinds.into_map(|v| v.freeze(freezer)),
            names: self.names,
            positional: self.positional,
            no_args: self.no_args,
            args: self.args,
            kwargs: self.kwargs,
        }
    }

    /// Used when performing garbage collection over a [`ParametersSpec`].
    pub fn walk(&mut self, walker: &Walker<'v>) {
        self.kinds.iter_mut().for_each(|x| x.walk(walker))
    }
}

pub(crate) struct ParametersCollect<'v, 'a, V> {
    params: ARef<'a, ParametersSpec<V>>,
    slots: Vec<ValueRef<'v>>,

    /// Initially true, becomes false once we see something not-positional.
    /// Required since we can fast-path positional if there are no conflicts.
    only_positional: bool,
    next_position: usize,
    args: Vec<Value<'v>>,
    kwargs: SmallMap<Value<'v>, Value<'v>>,
    // We defer errors right until the end, to simplify the API
    err: Option<anyhow::Error>,
}

impl<'v, 'a, V: ValueLike<'v>> ParametersCollect<'v, 'a, V> {
    fn set_err(&mut self, err: anyhow::Error) {
        if self.err.is_none() {
            self.err = Some(err);
        }
    }

    pub fn positional(&mut self, val: Value<'v>) {
        if self.next_position < self.params.positional {
            // Checking unassigned is moderately expensive, so use only_positional
            // which knows we have never set anything below next_position
            if self.only_positional || self.slots[self.next_position].is_unassigned() {
                self.slots[self.next_position].set(val);
                self.next_position += 1;
            } else {
                // Occurs if we have def f(a), then a=1, *[2]
                self.set_err(
                    FunctionError::RepeatedParameter {
                        name: self.params.param_name_at(self.next_position),
                    }
                    .into(),
                );
            }
        } else {
            self.args.push(val);
        }
    }

    pub fn named(&mut self, name: &str, name_value: Hashed<Value<'v>>, val: Value<'v>) {
        self.only_positional = false;
        // Safe to use new_unchecked because hash for the Value and str are the same
        let name_hash = BorrowHashed::new_unchecked(name_value.hash(), name);
        let repeated = match self.params.names.get_hashed(name_hash) {
            None => {
                let old = self.kwargs.insert_hashed(name_value, val);
                old.is_some()
            }
            Some(i) => {
                let res = !self.slots[*i].is_unassigned();
                self.slots[*i].set(val);
                res
            }
        };
        if repeated {
            self.set_err(
                FunctionError::RepeatedParameter {
                    name: name.to_owned(),
                }
                .into(),
            );
        }
    }

    pub fn args(&mut self, val: Value<'v>, heap: &'v Heap) {
        match val.iterate(heap) {
            Err(_) => self.set_err(FunctionError::ArgsArrayIsNotIterable.into()),
            Ok(iter) => {
                // It might be tempting to avoid iterating if it's going into the *args directly
                // But because lists are mutable that becomes observable behaviour, so we have
                // to copy the array
                for x in &iter {
                    self.positional(x);
                }
            }
        }
    }

    pub fn kwargs(&mut self, val: Value<'v>) {
        let res = try {
            match Dict::from_value(val) {
                Some(y) => {
                    // We know that reservation isn't too memory hungry,
                    // mostly because big maps don't actually properly reserve,
                    // so reserve assuming all of these values might go into kwargs
                    if self.params.kwargs.is_some() {
                        self.kwargs.reserve(y.len());
                    }
                    for (n, v) in y.iter_hashed() {
                        match n.key().unpack_str() {
                            None => Err(FunctionError::ArgsValueIsNotString)?,
                            Some(s) => self.named(s, n, v),
                        }
                    }
                }
                None => Err(FunctionError::KWArgsIsNotDict)?,
            }
        };
        match res {
            Err(v) => self.set_err(v),
            _ => {}
        }
    }

    pub(crate) fn done(self, heap: &'v Heap) -> anyhow::Result<Vec<ValueRef<'v>>> {
        let Self {
            params,
            mut slots,
            mut args,
            mut kwargs,
            err,
            ..
        } = self;
        if let Some(err) = err {
            return Err(err);
        }
        for ((index, def), ref slot) in params.kinds.iter().enumerate().zip(slots.iter_mut()) {
            if !slot.is_unassigned() {
                continue;
            }
            match def {
                ParameterKind::Required => {
                    return Err(FunctionError::MissingParameter {
                        name: params.param_name_at(index),
                        function: params.signature(),
                    }
                    .into());
                }
                ParameterKind::Optional => {}
                ParameterKind::Defaulted(x) => {
                    slot.set(x.to_value());
                }
                ParameterKind::Args => {
                    let args = mem::take(&mut args);
                    slot.set(heap.alloc(Tuple::new(args)));
                }
                ParameterKind::KWargs => {
                    let kwargs = mem::take(&mut kwargs);
                    slot.set(heap.alloc(Dict::new(kwargs)))
                }
            }
        }
        if !kwargs.is_empty() {
            return Err(FunctionError::ExtraNamedParameters {
                names: kwargs.keys().map(|x| x.to_str()).collect(),
                function: params.signature(),
            }
            .into());
        }
        if !args.is_empty() {
            return Err(FunctionError::ExtraPositionalParameters {
                count: args.len(),
                function: params.signature(),
            }
            .into());
        }
        Ok(slots)
    }
}

/// Parse a series of parameters which were specified by [`ParametersSpec`].
pub struct ParametersParser<'v, 'a> {
    slots: Iter<'a, Option<Value<'v>>>,
}

impl<'v, 'a> ParametersParser<'v, 'a> {
    pub(crate) fn new(slots: &'a [Option<Value<'v>>]) -> Self {
        Self {
            slots: slots.iter(),
        }
    }

    // Utility for improving the error message with more information
    fn named_err<T>(name: &str, x: Option<T>) -> anyhow::Result<T> {
        x.ok_or_else(|| ValueError::IncorrectParameterTypeNamed(name.to_owned()).into())
    }

    /// Obtain the next parameter, corresponding to [`ParametersSpec::optional`].
    /// It is an error to request more parameters than were specified.
    /// The `name` is only used for error messages.
    pub fn next_opt<T: UnpackValue<'v>>(&mut self, name: &str) -> anyhow::Result<Option<T>> {
        // This unwrap is safe because we only call next one time per ParametersSpec.count()
        // and slots starts out with that many entries.
        let v = self.slots.next().unwrap();
        match v {
            None => Ok(None),
            Some(v) => Ok(Some(Self::named_err(name, T::unpack_value(*v))?)),
        }
    }

    /// Obtain the next parameter, which can't be defined by [`ParametersSpec::optional`].
    /// It is an error to request more parameters than were specified.
    /// The `name` is only used for error messages.
    pub fn next<T: UnpackValue<'v>>(&mut self, name: &str) -> anyhow::Result<T> {
        // After ParametersCollect.done() all variables will be Some,
        // apart from those where we called ParametersSpec.optional(),
        // and for those we chould call next_opt()

        // This unwrap is safe because we only call next one time per ParametersSpec.count()
        // and slots starts out with that many entries.
        let v = self.slots.next().unwrap();
        // This is definitely not unassigned because ParametersCollect.done checked
        // that.
        let v = v.as_ref().unwrap();
        Self::named_err(name, T::unpack_value(*v))
    }
}
