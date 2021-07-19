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
    eval::{runtime::slots::LocalSlotBase, Evaluator},
    values::{
        dict::Dict, tuple::Tuple, Freezer, FrozenValue, Heap, Trace, Tracer, UnpackValue, Value,
        ValueError,
    },
};
use gazebo::{coerce::Coerce, prelude::*};
use std::{cmp, convert::TryInto};
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

#[derive(Debug, Clone, Coerce)]
#[repr(C)]
enum ParameterKind<V> {
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

// V = Value, or FrozenValue
#[derive(Debug, Clone)]
#[repr(C)]
pub struct ParametersSpecRaw<V> {
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

// Can't derive this since we don't want ParameterKind to be public
unsafe impl<From: Coerce<To>, To> Coerce<ParametersSpecRaw<To>> for ParametersSpecRaw<From> {}

/// A builder for [`ParametersSpec`].
#[derive(Debug, Clone)]
pub struct ParametersSpecBuilder<V>(ParametersSpecRaw<V>);

/// Define a list of parameters. This code assumes that all names are distinct and that
/// `*args`/`**kwargs` occur in well-formed locations.
#[derive(Debug, Clone, Coerce)]
#[repr(transparent)]
// V = Value, or FrozenValue
pub struct ParametersSpec<V>(ParametersSpecRaw<V>);

impl<V> ParametersSpecBuilder<V> {
    /// Create a new [`ParametersSpecBuilder`] with the given function name.
    pub fn new(function_name: String) -> Self {
        Self::with_capacity(function_name, 0)
    }

    /// Create a new [`ParametersSpecBuilder`] with the given function name and an advance capacity hint.
    pub fn with_capacity(function_name: String, capacity: usize) -> Self {
        Self(ParametersSpecRaw {
            function_name,
            kinds: Vec::with_capacity(capacity),
            names: SmallMap::with_capacity(capacity),
            positional: 0,
            no_args: false,
            args: None,
            kwargs: None,
        })
    }

    /// Change the function name.
    pub fn set_function_name(&mut self, name: String) {
        self.0.function_name = name
    }

    fn add(&mut self, name: &str, val: ParameterKind<V>) {
        let i = self.0.kinds.len();
        self.0.kinds.push(val);
        let old = self.0.names.insert(name.to_owned(), i);
        if self.0.args.is_none() && !self.0.no_args {
            // If you've already seen `args` or `no_args`, you can't enter these
            // positionally
            self.0.positional = i + 1;
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
    /// parameter. After this call, any subsequent [`required`](ParametersSpecBuilder::required),
    /// [`optional`](ParametersSpecBuilder::optional) or [`defaulted`](ParametersSpecBuilder::defaulted)
    /// parameters can _only_ be supplied by name.
    pub fn args(&mut self) {
        assert!(self.0.args.is_none() && !self.0.no_args);
        self.0.kinds.push(ParameterKind::Args);
        self.0.args = Some(self.0.kinds.len() - 1);
    }

    /// This function has no `*args` parameter, corresponds to the Python parameter `*`.
    /// After this call, any subsequent [`required`](ParametersSpecBuilder::required),
    /// [`optional`](ParametersSpecBuilder::optional) or [`defaulted`](ParametersSpecBuilder::defaulted)
    /// parameters can _only_ be supplied by name.
    pub fn no_args(&mut self) {
        assert!(self.0.args.is_none() && !self.0.no_args);
        self.0.no_args = true;
    }

    /// Add a `**kwargs` parameter which will be a dictionary, recorded into a [`SmallMap`].
    /// A function can only have one `kwargs` parameter.
    /// parameter. After this call, any subsequent [`required`](ParametersSpecBuilder::required),
    /// [`optional`](ParametersSpecBuilder::optional) or [`defaulted`](ParametersSpecBuilder::defaulted)
    /// parameters can _only_ be supplied by position.
    pub fn kwargs(&mut self) {
        assert!(self.0.kwargs.is_none());
        self.0.kinds.push(ParameterKind::KWargs);
        self.0.kwargs = Some(self.0.kinds.len() - 1);
    }

    pub fn build(self) -> ParametersSpec<V> {
        ParametersSpec(self.0)
    }
}

impl<V> ParametersSpec<V> {
    /// Produce an approximate signature for the function, combining the name and arguments.
    pub fn signature(&self) -> String {
        let mut collector = String::new();
        self.collect_repr(&mut collector);
        collector
    }

    /// Figure out the argument name at an index in kinds.
    /// Only called in the error path, so is not optimised.
    pub(crate) fn param_name_at(&self, index: usize) -> String {
        match self.0.kinds[index] {
            ParameterKind::Args => return "args".to_owned(),
            ParameterKind::KWargs => return "kwargs".to_owned(),
            _ => {}
        }
        // We want names[#index], ignoring all the args/kwargs up until this position
        let mut new_index = index;
        for k in self.0.kinds.iter().take(index) {
            match k {
                ParameterKind::Args | ParameterKind::KWargs => new_index -= 1,
                _ => {}
            }
        }
        self.0.names.get_index(new_index).unwrap().0.clone()
    }

    // Generate a good error message for it
    pub(crate) fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.0.function_name);
        collector.push('(');

        let mut names = self.0.names.keys();
        let mut next_name = || {
            // We prepend '$' on the front of variable names that are positional-only
            // arguments to the native functions. We rip those off when
            // displaying the signature.
            // The `unwrap` is safe because we must have a names entry for each
            // non-Args/KWargs kind.
            names.next().unwrap().trim_start_match('$')
        };

        for (i, typ) in self.0.kinds.iter().enumerate() {
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
    #[inline(always)]
    pub(crate) fn collect(
        &self,
        slots: usize,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<LocalSlotBase> {
        // Return true if the value is a duplicate
        #[inline(always)]
        fn add_kwargs<'v>(
            kwargs: &mut Option<Box<Dict<'v>>>,
            key: Hashed<Value<'v>>,
            val: Value<'v>,
        ) -> bool {
            match kwargs {
                None => {
                    // pick 11 as its the largest Vec we might need, but not yet a SmallMap
                    let mut mp = SmallMap::with_capacity(11);
                    mp.insert_hashed(key, val);
                    *kwargs = Some(box Dict::new(mp));
                    false
                }
                Some(mp) => mp.content.insert_hashed(key, val).is_some(),
            }
        }

        let len = self.0.kinds.len();
        let slot_base = eval.local_variables.reserve(cmp::max(slots, len));
        let slots = eval.local_variables.get_slots_at(slot_base);

        let mut args = Vec::new();
        let mut kwargs = None;
        let mut next_position = 0;

        // First deal with positional parameters
        if params.pos.len() <= self.0.positional {
            // fast path for when we don't need to bounce down to filling in args
            for (v, s) in params.pos.iter().zip(slots.iter()) {
                s.set_direct(*v);
            }
            if params.pos.len() == self.0.positional
                && params.pos.len() == self.0.kinds.len()
                && params.named.is_empty()
                && params.args.is_none()
                && params.kwargs.is_none()
            {
                // If the arguments equal the length and the kinds, and we don't have any other args,
                // then no_args, *args and **kwargs must all be unset,
                // and we don't have to crate args/kwargs objects, we can skip everything else
                return Ok(slot_base);
            }
            next_position = params.pos.len();
        } else {
            for v in params.pos {
                if next_position < self.0.positional {
                    slots[next_position].set_direct(*v);
                    next_position += 1;
                } else {
                    args.push(*v);
                }
            }
        }

        // Next deal with named parameters
        // The lowest position at which we've written a name.
        // If at the end lowest_name is less than next_position, we got the same variable twice.
        // So no duplicate checking until after all positional arguments
        let mut lowest_name = usize::MAX;
        // Avoid a lot of loop setup etc in the common case
        if !params.names.is_empty() {
            for ((name, name_value), v) in params.names.iter().zip(params.named) {
                // Safe to use new_unchecked because hash for the Value and str are the same
                let name_hash = BorrowHashed::new_unchecked(name_value.hash(), name);
                match self.0.names.get_hashed(name_hash) {
                    None => {
                        add_kwargs(&mut kwargs, *name_value, *v);
                    }
                    Some(i) => {
                        slots[*i].set_direct(*v);
                        lowest_name = cmp::min(lowest_name, *i);
                    }
                }
            }
        }

        // Next up are the *args parameters
        if let Some(param_args) = params.args {
            match param_args.iterate(eval.heap()) {
                Err(_) => return Err(FunctionError::ArgsArrayIsNotIterable.into()),
                Ok(iter) => {
                    for v in iter {
                        if next_position < self.0.positional {
                            slots[next_position].set_direct(v);
                            next_position += 1;
                        } else {
                            args.push(v);
                        }
                    }
                }
            }
        }

        // Check if the named arguments clashed with the positional arguments
        if next_position > lowest_name {
            return Err(FunctionError::RepeatedParameter {
                name: self.param_name_at(lowest_name),
            }
            .into());
        }

        // Now insert the kwargs, if there are any
        if let Some(param_kwargs) = params.kwargs {
            match Dict::from_value(param_kwargs) {
                Some(y) => {
                    for (k, v) in y.iter_hashed() {
                        match k.key().unpack_str() {
                            None => return Err(FunctionError::ArgsValueIsNotString.into()),
                            Some(s) => {
                                let name_hash = BorrowHashed::new_unchecked(k.hash(), s);
                                let repeat = match self.0.names.get_hashed(name_hash) {
                                    None => add_kwargs(&mut kwargs, k, v),
                                    Some(i) => {
                                        let this_slot = &slots[*i];
                                        let repeat = this_slot.get_direct().is_some();
                                        this_slot.set_direct(v);
                                        repeat
                                    }
                                };
                                if repeat {
                                    return Err(FunctionError::RepeatedParameter {
                                        name: s.to_owned(),
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
        let kinds = &self.0.kinds;
        // This code is very hot, and setting up iterators was a noticeable bottleneck.
        for index in next_position..kinds.len() {
            // The number of locals must be at least the number of parameters, see `collect`
            // which reserves `max(_, kinds.len())`.
            let slot = unsafe { slots.get_unchecked(index) };
            let def = unsafe { kinds.get_unchecked(index) };

            // We know that up to next_position got filled positionally, so we don't need to check those
            if slot.get_direct().is_some() {
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
                    slot.set_direct(*x);
                }
                _ => {}
            }
        }

        // Now set the kwargs/args slots, if they are requested, and fail it they are absent but used
        // Note that we deliberately give warnings about missing parameters _before_ giving warnings
        // about unexpected extra parameters, so if a user mis-spells an argument they get a better error.
        if let Some(args_pos) = self.0.args {
            slots[args_pos].set_direct(eval.heap().alloc(Tuple::new(args)));
        } else if !args.is_empty() {
            return Err(FunctionError::ExtraPositionalParameters {
                count: args.len(),
                function: self.signature(),
            }
            .into());
        }

        if let Some(kwargs_pos) = self.0.kwargs {
            let kwargs = kwargs.take().unwrap_or_default();
            slots[kwargs_pos].set_direct(eval.heap().alloc(*kwargs));
        } else if let Some(kwargs) = kwargs {
            return Err(FunctionError::ExtraNamedParameters {
                names: kwargs.content.keys().map(|x| x.to_str()).collect(),
                function: self.signature(),
            }
            .into());
        }
        Ok(slot_base)
    }
}

unsafe impl<'v, T: Trace<'v>> Trace<'v> for ParametersSpec<T> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.0.kinds.iter_mut().for_each(|x| x.trace(tracer))
    }
}

impl<'v> ParametersSpec<Value<'v>> {
    /// Used to freeze a [`ParametersSpec`].
    pub fn freeze(self, freezer: &Freezer) -> anyhow::Result<ParametersSpec<FrozenValue>> {
        Ok(ParametersSpec(ParametersSpecRaw {
            function_name: self.0.function_name,
            kinds: self.0.kinds.try_map(|v| v.freeze(freezer))?,
            names: self.0.names,
            positional: self.0.positional,
            no_args: self.0.no_args,
            args: self.0.args,
            kwargs: self.0.kwargs,
        }))
    }
}

/// Parse a series of parameters which were specified by [`ParametersSpec`].
pub struct ParametersParser {
    base: LocalSlotBase,
    next: usize,
}

impl ParametersParser {
    pub(crate) fn new(base: LocalSlotBase) -> Self {
        Self { base, next: 0 }
    }

    // Utility for improving the error message with more information
    fn named_err<T>(name: &str, x: Option<T>) -> anyhow::Result<T> {
        x.ok_or_else(|| ValueError::IncorrectParameterTypeNamed(name.to_owned()).into())
    }

    fn get_next<'v>(&mut self, eval: &Evaluator<'v, '_>) -> Option<Value<'v>> {
        let v = eval
            .local_variables
            .get_slot_at(self.base, self.next)
            .get_direct();
        self.next += 1;
        v
    }

    pub fn this<'v, T: UnpackValue<'v>>(&self, this: Option<Value<'v>>) -> anyhow::Result<T> {
        Self::named_err("this", this.and_then(T::unpack_value))
    }

    /// Obtain the next parameter, corresponding to [`ParametersSpecBuilder::optional`].
    /// It is an error to request more parameters than were specified.
    /// The `name` is only used for error messages.
    pub fn next_opt<'v, T: UnpackValue<'v>>(
        &mut self,
        name: &str,
        eval: &Evaluator<'v, '_>,
    ) -> anyhow::Result<Option<T>> {
        match self.get_next(eval) {
            None => Ok(None),
            Some(v) => Ok(Some(Self::named_err(name, T::unpack_value(v))?)),
        }
    }

    /// Obtain the next parameter, which can't be defined by [`ParametersSpecBuilder::optional`].
    /// It is an error to request more parameters than were specified.
    /// The `name` is only used for error messages.
    pub fn next<'v, T: UnpackValue<'v>>(
        &mut self,
        name: &str,
        eval: &Evaluator<'v, '_>,
    ) -> anyhow::Result<T> {
        // After ParametersCollect.done() all variables will be Some,
        // apart from those where we called ParametersSpec.optional(),
        // and for those we chould call next_opt()

        // This is definitely not unassigned because ParametersCollect.done checked
        // that.
        let v = self.get_next(eval).unwrap();
        Self::named_err(name, T::unpack_value(v))
    }
}

#[derive(Default, Clone, Copy, Dupe)]
pub struct Parameters<'v, 'a> {
    pub this: Option<Value<'v>>,
    pub pos: &'a [Value<'v>],
    pub named: &'a [Value<'v>],
    pub names: &'a [(String, Hashed<Value<'v>>)],
    pub args: Option<Value<'v>>,
    pub kwargs: Option<Value<'v>>,
}

impl<'v, 'a> Parameters<'v, 'a> {
    /// Produce [`Err`] if there are any named (i.e. non-positional) arguments.
    #[inline(always)]
    fn pos_only(&self) -> anyhow::Result<()> {
        #[cold]
        #[inline(never)]
        fn bad(x: &Parameters) -> anyhow::Result<()> {
            // We might have a empty kwargs dictionary, but probably have an error
            let mut extra = Vec::new();
            extra.extend(x.names.iter().map(|x| x.0.clone()));
            if let Some(kwargs) = x.kwargs {
                match Dict::from_value(kwargs) {
                    None => return Err(FunctionError::KwArgsIsNotDict.into()),
                    Some(x) => {
                        for k in x.content.keys() {
                            match k.unpack_str() {
                                None => return Err(FunctionError::ArgsValueIsNotString.into()),
                                Some(k) => extra.push(k.to_owned()),
                            }
                        }
                    }
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

    /// Collect exactly `N` positional arguments from the [`Parameters`], failing if there are too many/few
    /// arguments, or if there are any named arguments.
    #[inline(always)]
    pub fn positional<const N: usize>(&self, heap: &'v Heap) -> anyhow::Result<[Value<'v>; N]> {
        #[cold]
        #[inline(never)]
        fn rare<'v, const N: usize>(
            x: &Parameters<'v, '_>,
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

        self.pos_only()?;
        if self.args.is_none() {
            self.pos
                .try_into()
                .map_err(|_| FunctionError::WrongNumberOfParameters(N, N, self.pos.len()).into())
        } else {
            rare(self, heap)
        }
    }

    /// Collect exactly `REQUIRED` positional arguments, plus at most `OPTIONAL` positional arguments
    /// from the [`Parameters`], failing if there are too many/few arguments, or if there are any named arguments.
    /// The `OPTIONAL` array will never have a [`Some`] after a [`None`].
    #[inline(always)]
    pub fn optional<const REQUIRED: usize, const OPTIONAL: usize>(
        &self,
        heap: &'v Heap,
    ) -> anyhow::Result<([Value<'v>; REQUIRED], [Option<Value<'v>>; OPTIONAL])> {
        #[cold]
        #[inline(never)]
        fn rare<'v, const REQUIRED: usize, const OPTIONAL: usize>(
            x: &Parameters<'v, '_>,
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

        self.pos_only()?;
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
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parameter_unpack() {
        let heap = Heap::new();
        fn f<'v, F: Fn(&Parameters<'v, '_>), const N: usize>(heap: &'v Heap, op: F) {
            for i in 0..=N {
                let mut p = Parameters::default();
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
    fn test_parameter_unpack_named() {
        let heap = Heap::new();
        let mut p = Parameters::default();
        assert!(p.positional::<0>(&heap).is_ok());

        // Test lots of forms of kwargs work properly
        p.kwargs = Some(Value::new_none());
        assert!(p.positional::<0>(&heap).is_err());
        p.kwargs = Some(heap.alloc(Dict::default()));
        assert!(p.positional::<0>(&heap).is_ok());
        let mut sm = SmallMap::new();
        sm.insert_hashed(heap.alloc("test").get_hashed().unwrap(), Value::new_none());
        p.kwargs = Some(heap.alloc(Dict::new(sm)));
        assert!(p.positional::<0>(&heap).is_err());

        // Test named arguments work properly
        p.kwargs = None;
        let named = [Value::new_none()];
        p.named = &named;
        let names = [("test".to_owned(), heap.alloc("test").get_hashed().unwrap())];
        p.names = &names;
        assert!(p.positional::<0>(&heap).is_err());
        assert!(p.positional::<1>(&heap).is_err());
    }
}
