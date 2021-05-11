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

//! Implementation of `def`.

use crate::{
    codemap::CodeMap,
    environment::{slots::LocalSlots, FrozenModuleValue},
    eval::{
        compiler::{scope::ScopeNames, Compiler, EvalCompiled, EvalException},
        runtime::{evaluator::Evaluator, parameters::ParametersSpec},
    },
    syntax::ast::{AstExpr, AstParameter, AstStmt, Parameter},
    values::{
        function::{FunctionInvoker, FunctionInvokerInner, FUNCTION_TYPE},
        AllocValue, ComplexValue, Freezer, FrozenValue, Heap, SimpleValue, StarlarkValue, Value,
        ValueLike, ValueRef, Walker,
    },
};
use derivative::Derivative;
use gazebo::{cell::ARef, prelude::*};
use std::sync::Arc;

enum ParameterCompiled {
    Normal(String, Option<EvalCompiled>),
    WithDefaultValue(String, Option<EvalCompiled>, EvalCompiled),
    NoArgs,
    Args(String, Option<EvalCompiled>),
    KwArgs(String, Option<EvalCompiled>),
}

impl ParameterCompiled {
    fn name(&self) -> Option<&str> {
        match self {
            Self::Normal(x, _) => Some(x),
            Self::WithDefaultValue(x, _, _) => Some(x),
            Self::NoArgs => None,
            Self::Args(x, _) => Some(x),
            Self::KwArgs(x, _) => Some(x),
        }
    }

    fn ty(&self) -> Option<&EvalCompiled> {
        match self {
            Self::Normal(_, t) => t.as_ref(),
            Self::WithDefaultValue(_, t, _) => t.as_ref(),
            Self::NoArgs => None,
            Self::Args(_, t) => t.as_ref(),
            Self::KwArgs(_, t) => t.as_ref(),
        }
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
struct DefInfo {
    scope_names: ScopeNames,
    // The compiled expression for the body of this definition, to be run
    // after the parameters are evaluated.
    #[derivative(Debug = "ignore")]
    body: EvalCompiled,
}

impl Compiler<'_> {
    fn parameter(&mut self, x: AstParameter) -> ParameterCompiled {
        match x.node {
            Parameter::Normal(x, t) => ParameterCompiled::Normal(x.node, self.expr_opt(t)),
            Parameter::WithDefaultValue(x, t, v) => {
                ParameterCompiled::WithDefaultValue(x.node, self.expr_opt(t), self.expr(*v))
            }
            Parameter::NoArgs => ParameterCompiled::NoArgs,
            Parameter::Args(x, t) => ParameterCompiled::Args(x.node, self.expr_opt(t)),
            Parameter::KwArgs(x, t) => ParameterCompiled::KwArgs(x.node, self.expr_opt(t)),
        }
    }

    pub fn function(
        &mut self,
        name: &str,
        params: Vec<AstParameter>,
        return_type: Option<Box<AstExpr>>,
        suite: AstStmt,
    ) -> EvalCompiled {
        let file = self.codemap.look_up_span(suite.span);
        let function_name = format!("{}.{}", file.file.name(), name);

        // The parameters run in the scope of the parent, so compile them with the outer
        // scope
        let params = params.into_map(|x| self.parameter(x));
        let return_type = self.expr_opt(return_type);

        self.scope
            .enter_def(params.iter().flat_map(ParameterCompiled::name), &suite);
        let body = self.stmt(suite);
        let scope_names = self.scope.exit_def();

        let info = Arc::new(DefInfo { scope_names, body });

        fn run<'v>(
            x: &Option<EvalCompiled>,
            context: &mut Evaluator<'v, '_>,
        ) -> Result<(), EvalException<'v>> {
            if let Some(v) = x {
                v(context)?;
            }
            Ok(())
        }

        box move |context| {
            let mut parameters =
                ParametersSpec::with_capacity(function_name.to_owned(), params.len());
            let mut parameter_types = Vec::new();

            for (i, x) in params.iter().enumerate() {
                if let Some(t) = x.ty() {
                    let v = t(context)?;
                    let name = x.name().unwrap_or("unknown").to_owned();
                    parameter_types.push((i, name, v));
                }

                match x {
                    ParameterCompiled::Normal(n, t) => {
                        run(t, context)?;
                        parameters.required(n)
                    }
                    ParameterCompiled::WithDefaultValue(n, t, v) => {
                        run(t, context)?;
                        parameters.defaulted(n, v(context)?);
                    }
                    ParameterCompiled::NoArgs => parameters.no_args(),
                    ParameterCompiled::Args(_, t) => {
                        run(t, context)?;
                        parameters.args()
                    }
                    ParameterCompiled::KwArgs(_, t) => {
                        run(t, context)?;
                        parameters.kwargs()
                    }
                }
            }
            let return_type = match &return_type {
                None => None,
                Some(v) => Some(v(context)?),
            };
            Ok(Def::new(
                parameters,
                parameter_types,
                return_type,
                info.dupe(),
                context.codemap.dupe(),
                context,
            ))
        }
    }
}

/// Starlark function internal representation and implementation of
/// [`StarlarkValue`].
#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct DefGen<V, RefV> {
    parameters: ParametersSpec<V>, // The parameters, **kwargs etc including defaults (which are evaluated afresh each time)
    parameter_types: Vec<(usize, String, V)>, // The types of the parameters (sparse indexed array, (0, argm T) implies parameter 0 named arg must have type T)
    return_type: Option<V>,                   // The return type annotation for the function
    codemap: CodeMap,                         // Codemap that was active during this module
    stmt: Arc<DefInfo>,                       // The source code and metadata for this function
    captured: Vec<RefV>, // Any variables captured from the outer scope (nested def/lambda), see stmt.parent
    // Important to ignore these field as it probably references DefGen in a cycle
    #[derivative(Debug = "ignore")]
    module: Option<FrozenModuleValue>, // A reference to the module variables, if we have been frozen
}

// We can't use the `starlark_complex_value!` macro because we have two type arguments.
pub(crate) type Def<'v> = DefGen<Value<'v>, ValueRef<'v>>;
pub(crate) type FrozenDef = DefGen<FrozenValue, FrozenValue>;

any_lifetime!(Def<'v>);
any_lifetime!(FrozenDef);

impl<'v> Def<'v> {
    fn new(
        parameters: ParametersSpec<Value<'v>>,
        parameter_types: Vec<(usize, String, Value<'v>)>,
        return_type: Option<Value<'v>>,
        stmt: Arc<DefInfo>,
        codemap: CodeMap,
        context: &mut Evaluator<'v, '_>,
    ) -> Value<'v> {
        let captured = stmt
            .scope_names
            .parent
            .map(|(x, _)| context.clone_slot_reference(*x, context.heap()));
        context.heap().alloc(Self {
            parameters,
            parameter_types,
            return_type,
            stmt,
            codemap,
            captured,
            module: None,
        })
    }
}

impl<T1, T2> DefGen<T1, T2> {
    pub(crate) fn scope_names(&self) -> &ScopeNames {
        &self.stmt.scope_names
    }
}

impl SimpleValue for FrozenDef {}

impl<'v> ComplexValue<'v> for Def<'v> {
    fn freeze(self: Box<Self>, freezer: &Freezer) -> Box<dyn SimpleValue> {
        let parameters = self.parameters.freeze(freezer);
        let parameter_types = self
            .parameter_types
            .into_map(|(i, s, v)| (i, s, v.freeze(freezer)));
        let return_type = self.return_type.map(|v| v.freeze(freezer));
        let captured = self.captured.map(|x| x.freeze(freezer));
        box FrozenDef {
            parameters,
            parameter_types,
            return_type,
            codemap: self.codemap,
            stmt: self.stmt,
            captured,
            module: Some(FrozenModuleValue::new(freezer)),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        self.parameters.walk(walker);
        for (_, _, v) in self.parameter_types.iter_mut() {
            walker.walk(v)
        }
        for v in self.return_type.iter_mut() {
            walker.walk(v)
        }
        for x in self.captured.iter() {
            walker.walk_ref(x)
        }
    }
}

impl<'v> AllocValue<'v> for Def<'v> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_complex(self)
    }
}

// We define two different StarlarkValue instances because
// the invoker uses different types for both of them.
impl<'v> StarlarkValue<'v> for FrozenDef {
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.parameters.signature());
    }

    fn new_invoker<'a>(
        &self,
        me: Value<'v>,
        _heap: &'v Heap,
    ) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        Ok(DefInvokerFrozen::new_frozen(ARef::map(
            me.get_aref(),
            |x| x.as_dyn_any().downcast_ref::<Self>().unwrap(),
        )))
    }
}

impl<'v> StarlarkValue<'v> for Def<'v> {
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.parameters.signature());
    }

    fn new_invoker<'a>(
        &self,
        me: Value<'v>,
        _heap: &'v Heap,
    ) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        Ok(DefInvoker::new(ARef::map(me.get_aref(), |x| {
            x.as_dyn_any().downcast_ref::<Self>().unwrap()
        })))
    }
}

pub(crate) type DefInvoker<'v, 'a> = DefInvokerGen<'a, Value<'v>, ValueRef<'v>>;
pub(crate) type DefInvokerFrozen<'a> = DefInvokerGen<'a, FrozenValue, FrozenValue>;

pub(crate) struct DefInvokerGen<'a, V, RefV>(ARef<'a, DefGen<V, RefV>>);

pub(crate) trait AsValueRef<'v> {
    fn to_value_ref(&self) -> ValueRef<'v>;
}

impl<'v> AsValueRef<'v> for FrozenValue {
    fn to_value_ref(&self) -> ValueRef<'v> {
        ValueRef::new_frozen(*self)
    }
}

impl<'v> AsValueRef<'v> for ValueRef<'v> {
    fn to_value_ref(&self) -> ValueRef<'v> {
        self.dupe()
    }
}

impl<'v, 'a> DefInvoker<'v, 'a> {
    fn new(def: ARef<'a, Def<'v>>) -> FunctionInvoker<'v, 'a> {
        let slots = def.stmt.scope_names.used;
        let (def, params) = ARef::map_split(def, |x| (x, &x.parameters));
        FunctionInvoker {
            collect: ParametersSpec::collect(params, slots),
            invoke: FunctionInvokerInner::Def(DefInvokerGen(def)),
        }
    }
}

impl<'a> DefInvokerFrozen<'a> {
    fn new_frozen<'v>(def: ARef<'a, FrozenDef>) -> FunctionInvoker<'v, 'a> {
        let slots = def.stmt.scope_names.used;
        let (def, params) = ARef::map_split(def, |x| (x, x.parameters.promote()));
        FunctionInvoker {
            collect: ParametersSpec::collect(params, slots),
            invoke: FunctionInvokerInner::DefFrozen(DefInvokerGen(def)),
        }
    }
}

impl<'a, 'v, V: ValueLike<'v>, RefV: AsValueRef<'v>> DefInvokerGen<'a, V, RefV> {
    pub fn invoke(
        self,
        slots: Vec<ValueRef<'v>>,
        context: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        // println!("invoking {}", self.def.stmt.name.node);
        let DefInvokerGen(def) = self;

        if context.check_types() {
            for (i, arg_name, ty) in &def.parameter_types {
                match slots[*i].get() {
                    None => panic!("Not allowed optional unassigned with type annotations on them"),
                    Some(v) => v.check_type(ty.to_value(), Some(arg_name))?,
                }
            }
        }

        let mut locals = LocalSlots::new(slots);

        // Copy over the parent slots
        for ((_, me), captured) in def.stmt.scope_names.parent.iter().zip(def.captured.iter()) {
            locals.set_slot_ref(*me, captured.to_value_ref());
        }

        let res =
            context.with_function_context(def.module, locals, def.codemap.dupe(), |context| {
                (def.stmt.body)(context)
            });

        let ret = match res {
            Err(EvalException::Return(ret)) => ret,
            Err(e) => return Err(e.into()),
            Ok(_) => Value::new_none(),
        };

        if context.check_types() {
            // Slightly ugly: by the time we check the return type, we no longer
            // have the location of the return statement, so the "blame" is attached
            // to the caller, rather than the return statement. Fixing it requires
            // either passing the type down (ugly) or passing the location back
            // (ugly and fiddly). Both also imply some runtime cost. If types take off,
            // worth revisiting.
            if let Some(t) = def.return_type {
                ret.check_type(t.to_value(), None)?
            }
        }
        Ok(ret)
    }
}
