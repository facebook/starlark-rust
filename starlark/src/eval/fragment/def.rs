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
    codemap::{CodeMap, Span},
    environment::FrozenModuleValue,
    eval::{
        compiler::{
            scope::ScopeNames, Compiler, EvalException, ExprCompiled, ExprCompiledValue,
            StmtCompiled,
        },
        runtime::{
            evaluator::Evaluator,
            parameters::ParametersSpec,
            slots::{LocalSlotBase, LocalSlotId},
        },
        Parameters,
    },
    syntax::ast::{AstExpr, AstParameter, AstStmt, Parameter},
    values::{
        function::FUNCTION_TYPE, typing::TypeCompiled, ComplexValue, Freezer, FrozenValue,
        StarlarkValue, Trace, Tracer, Value, ValueLike, ValueRef,
    },
};
use derivative::Derivative;
use gazebo::prelude::*;
use std::sync::Arc;

enum ParameterCompiled<T> {
    Normal(String, Option<T>),
    WithDefaultValue(String, Option<T>, T),
    NoArgs,
    Args(String, Option<T>),
    KwArgs(String, Option<T>),
}

impl<T> ParameterCompiled<T> {
    fn name(&self) -> Option<&str> {
        match self {
            Self::Normal(x, _) => Some(x),
            Self::WithDefaultValue(x, _, _) => Some(x),
            Self::NoArgs => None,
            Self::Args(x, _) => Some(x),
            Self::KwArgs(x, _) => Some(x),
        }
    }

    fn ty(&self) -> Option<&T> {
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
    body: StmtCompiled,
}

impl Compiler<'_> {
    fn parameter(&mut self, x: AstParameter) -> ParameterCompiled<ExprCompiled> {
        match x.node {
            Parameter::Normal(x, t) => ParameterCompiled::Normal(
                x.node,
                self.expr_opt(t).map(ExprCompiledValue::as_compiled),
            ),
            Parameter::WithDefaultValue(x, t, v) => ParameterCompiled::WithDefaultValue(
                x.node,
                self.expr_opt(t).map(ExprCompiledValue::as_compiled),
                self.expr(*v).as_compiled(),
            ),
            Parameter::NoArgs => ParameterCompiled::NoArgs,
            Parameter::Args(x, t) => ParameterCompiled::Args(
                x.node,
                self.expr_opt(t).map(ExprCompiledValue::as_compiled),
            ),
            Parameter::KwArgs(x, t) => ParameterCompiled::KwArgs(
                x.node,
                self.expr_opt(t).map(ExprCompiledValue::as_compiled),
            ),
        }
    }

    pub fn function(
        &mut self,
        name: &str,
        params: Vec<AstParameter>,
        return_type: Option<Box<AstExpr>>,
        suite: AstStmt,
    ) -> ExprCompiledValue {
        let file = self.codemap.file_span(suite.span);
        let function_name = format!("{}.{}", file.file.filename(), name);

        // The parameters run in the scope of the parent, so compile them with the outer
        // scope
        let params = params.into_map(|x| self.parameter(x));
        let return_type = self
            .expr_opt(return_type)
            .map(ExprCompiledValue::as_compiled);

        self.scope
            .enter_def(params.iter().flat_map(ParameterCompiled::name), &suite);
        let body = self.stmt(suite, false);
        let scope_names = self.scope.exit_def();

        let info = Arc::new(DefInfo { scope_names, body });

        expr!("def", |eval| {
            let mut parameters =
                ParametersSpec::with_capacity(function_name.to_owned(), params.len());
            let mut parameter_types = Vec::new();

            for (i, x) in params.iter().enumerate() {
                if let Some(t) = x.ty() {
                    let v = t(eval)?;
                    let name = x.name().unwrap_or("unknown").to_owned();
                    parameter_types.push((i, name, v, TypeCompiled::new(v, eval.heap())?));
                }

                match x {
                    ParameterCompiled::Normal(n, _) => parameters.required(n),
                    ParameterCompiled::WithDefaultValue(n, _, v) => {
                        parameters.defaulted(n, v(eval)?);
                    }
                    ParameterCompiled::NoArgs => parameters.no_args(),
                    ParameterCompiled::Args(_, _) => parameters.args(),
                    ParameterCompiled::KwArgs(_, _) => parameters.kwargs(),
                }
            }
            let return_type = match &return_type {
                None => None,
                Some(v) => {
                    let v = v(eval)?;
                    Some((v, TypeCompiled::new(v, eval.heap())?))
                }
            };
            Def::new(
                parameters,
                parameter_types,
                return_type,
                info.dupe(),
                eval.codemap.dupe(),
                eval,
            )
        })
    }
}

/// Starlark function internal representation and implementation of
/// [`StarlarkValue`].
#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct DefGen<V, RefV> {
    parameters: ParametersSpec<V>, // The parameters, **kwargs etc including defaults (which are evaluated afresh each time)
    parameter_types: Vec<(usize, String, V, TypeCompiled)>, // The types of the parameters (sparse indexed array, (0, argm T) implies parameter 0 named arg must have type T)
    return_type: Option<(V, TypeCompiled)>, // The return type annotation for the function
    codemap: CodeMap,                       // Codemap that was active during this module
    stmt: Arc<DefInfo>,                     // The source code and metadata for this function
    captured: Vec<RefV>, // Any variables captured from the outer scope (nested def/lambda), see stmt.parent
    // Important to ignore these field as it probably references DefGen in a cycle
    #[derivative(Debug = "ignore")]
    module: Option<FrozenModuleValue>, // A reference to the module variables, if we have been frozen
}

// We can't use the `starlark_complex_value!` macro because we have two type arguments.
pub(crate) type Def<'v> = DefGen<Value<'v>, ValueRef<'v>>;
pub(crate) type FrozenDef = DefGen<FrozenValue, Option<FrozenValue>>;

starlark_complex_values!(Def);

impl<'v> Def<'v> {
    fn new(
        parameters: ParametersSpec<Value<'v>>,
        parameter_types: Vec<(usize, String, Value<'v>, TypeCompiled)>,
        return_type: Option<(Value<'v>, TypeCompiled)>,
        stmt: Arc<DefInfo>,
        codemap: CodeMap,
        eval: &mut Evaluator<'v, '_>,
    ) -> Value<'v> {
        let captured = stmt
            .scope_names
            .parent
            .map(|(x, _)| eval.clone_slot_reference(*x, eval.heap()));
        eval.heap().alloc(Self {
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

unsafe impl<'v> Trace<'v> for Def<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        self.parameters.trace(tracer);
        for (_, _, x, _) in self.parameter_types.iter_mut() {
            x.trace(tracer);
        }
        for (x, _) in self.return_type.iter_mut() {
            x.trace(tracer);
        }
        for x in self.captured.iter_mut() {
            x.trace(tracer);
        }
    }
}

impl<'v> ComplexValue<'v> for Def<'v> {
    type Frozen = FrozenDef;

    fn freeze(self, freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        let parameters = self.parameters.freeze(freezer)?;
        let parameter_types = self
            .parameter_types
            .into_try_map(|(i, s, v, t)| Ok::<_, anyhow::Error>((i, s, v.freeze(freezer)?, t)))?;
        let return_type = self
            .return_type
            .into_try_map(|(v, t)| Ok::<_, anyhow::Error>((v.freeze(freezer)?, t)))?;
        let captured = self.captured.try_map(|x| x.freeze(freezer))?;
        Ok(FrozenDef {
            parameters,
            parameter_types,
            return_type,
            codemap: self.codemap,
            stmt: self.stmt,
            captured,
            module: Some(FrozenModuleValue::new(freezer)),
        })
    }
}

// We define two different StarlarkValue instances because
// the invoker uses different types for both of them.
impl<'v> StarlarkValue<'v> for FrozenDef {
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.parameters.signature());
    }

    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        eval.ann("invoke_frozen_def", |eval| {
            let local_slots = self.stmt.scope_names.used;
            let slot_base = eval.local_variables.reserve(local_slots);
            let slots = eval.local_variables.get_slots_at(slot_base);
            self.parameters.collect_inline(params, slots, eval.heap())?;
            eval.with_call_stack(me, location, |eval| {
                eval.ann("invoke_frozen_def_raw", |eval| {
                    self.invoke_raw(slot_base, eval)
                })
            })
        })
    }
}

impl<'v> StarlarkValue<'v> for Def<'v> {
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.parameters.signature());
    }

    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        params: Parameters<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        eval.ann("invoke_def", |eval| {
            let local_slots = self.stmt.scope_names.used;
            let slot_base = eval.local_variables.reserve(local_slots);
            let slots = eval.local_variables.get_slots_at(slot_base);
            self.parameters.collect_inline(params, slots, eval.heap())?;
            eval.with_call_stack(me, location, |eval| {
                eval.ann("invoke_def_raw", |eval| self.invoke_raw(slot_base, eval))
            })
        })
    }
}

pub(crate) trait AsValueRef<'v> {
    fn to_value_ref(&self) -> ValueRef<'v>;
}

impl<'v> AsValueRef<'v> for Option<FrozenValue> {
    fn to_value_ref(&self) -> ValueRef<'v> {
        ValueRef::new_frozen(*self)
    }
}

impl<'v> AsValueRef<'v> for ValueRef<'v> {
    fn to_value_ref(&self) -> ValueRef<'v> {
        self.dupe_reference()
    }
}

impl<'v, V: ValueLike<'v>, RefV: AsValueRef<'v>> DefGen<V, RefV> {
    pub fn invoke_raw(
        &self,
        locals: LocalSlotBase,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        // println!("invoking {}", self.def.stmt.name.node);
        let old_locals = eval.local_variables.utilise(locals);

        if eval.check_types() {
            for (i, arg_name, ty, ty2) in &self.parameter_types {
                match eval.get_slot_local(LocalSlotId::new(*i), arg_name.as_str()) {
                    Err(_) => {
                        panic!("Not allowed optional unassigned with type annotations on them")
                    }
                    Ok(v) => v.check_type_compiled(ty.to_value(), ty2, Some(arg_name))?,
                }
            }
        }

        // Copy over the parent slots
        for ((_, me), captured) in self
            .stmt
            .scope_names
            .parent
            .iter()
            .zip(self.captured.iter())
        {
            eval.local_variables
                .set_slot_ref(*me, captured.to_value_ref());
        }

        let res =
            eval.with_function_context(self.module, &self.codemap, |eval| (self.stmt.body)(eval));
        eval.local_variables.release(old_locals);

        let ret = match res {
            Err(EvalException::Return(ret)) => ret,
            Err(e) => return Err(e.into()),
            Ok(_) => Value::new_none(),
        };

        if eval.check_types() {
            // Slightly ugly: by the time we check the return type, we no longer
            // have the location of the return statement, so the "blame" is attached
            // to the caller, rather than the return statement. Fixing it requires
            // either passing the type down (ugly) or passing the location back
            // (ugly and fiddly). Both also imply some runtime cost. If types take off,
            // worth revisiting.
            if let Some((tv, t)) = &self.return_type {
                ret.check_type_compiled(tv.to_value(), t, None)?
            }
        }
        Ok(ret)
    }
}
