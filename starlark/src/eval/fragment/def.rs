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
    codemap::{CodeMap, Span, Spanned},
    environment::FrozenModuleValue,
    eval::{
        compiler::{
            expr_throw,
            scope::{
                Captured, CstAssignIdent, CstExpr, CstParameter, CstStmt, ScopeId, ScopeNames,
            },
            throw_eval_exception, Compiler, EvalException,
        },
        fragment::{
            expr::{ExprCompiled, ExprCompiledValue, MaybeNot},
            stmt::{StmtCompiled, StmtCompiledValue, StmtsCompiled},
        },
        runtime::{
            arguments::{ParameterKind, ParametersSpec},
            evaluator::Evaluator,
            slots::{LocalSlotBase, LocalSlotId},
        },
        Arguments,
    },
    syntax::ast::ParameterP,
    values::{
        docs,
        docs::{DocItem, DocString},
        function::FUNCTION_TYPE,
        typing::TypeCompiled,
        ComplexValue, Freezer, FrozenStringValue, FrozenValue, StarlarkValue, Trace, Tracer, Value,
        ValueLike,
    },
};
use derivative::Derivative;
use gazebo::{any::AnyLifetime, prelude::*};
use std::{collections::HashMap, mem, sync::Arc};

struct ParameterName {
    name: String,
    captured: Captured,
}

enum ParameterCompiled<T> {
    Normal(ParameterName, Option<T>),
    WithDefaultValue(ParameterName, Option<T>, T),
    NoArgs,
    Args(ParameterName, Option<T>),
    KwArgs(ParameterName, Option<T>),
}

impl<T> ParameterCompiled<T> {
    fn param_name(&self) -> Option<&ParameterName> {
        match self {
            Self::Normal(x, _) => Some(x),
            Self::WithDefaultValue(x, _, _) => Some(x),
            Self::NoArgs => None,
            Self::Args(x, _) => Some(x),
            Self::KwArgs(x, _) => Some(x),
        }
    }

    fn accepts_positional(&self) -> bool {
        match self {
            ParameterCompiled::Normal(_, _) => true,
            ParameterCompiled::WithDefaultValue(_, _, _) => true,
            _ => false,
        }
    }

    fn name(&self) -> Option<&str> {
        self.param_name().map(|n| n.name.as_str())
    }

    fn captured(&self) -> Captured {
        self.param_name().map_or(Captured::No, |n| n.captured)
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
pub(crate) struct DefInfo {
    scope_names: ScopeNames,
    // The compiled expression for the body of this definition, to be run
    // after the parameters are evaluated.
    #[derivative(Debug = "ignore")]
    body: StmtCompiled,
    /// Function body is `type(x) == "y"`
    pub(crate) returns_type_is: Option<FrozenStringValue>,
}

impl Compiler<'_> {
    fn parameter_name(&mut self, ident: CstAssignIdent) -> ParameterName {
        let binding_id = ident.1.expect("no binding for parameter");
        let binding = self.scope_data.get_binding(binding_id);
        ParameterName {
            name: ident.node.0,
            captured: binding.captured,
        }
    }

    fn parameter(&mut self, x: CstParameter) -> Spanned<ParameterCompiled<ExprCompiled>> {
        Spanned {
            span: x.span,
            node: match x.node {
                ParameterP::Normal(x, t) => ParameterCompiled::Normal(
                    self.parameter_name(x),
                    self.expr_opt(t).map(ExprCompiledValue::as_compiled),
                ),
                ParameterP::WithDefaultValue(x, t, v) => ParameterCompiled::WithDefaultValue(
                    self.parameter_name(x),
                    self.expr_opt(t).map(ExprCompiledValue::as_compiled),
                    self.expr(*v).as_compiled(),
                ),
                ParameterP::NoArgs => ParameterCompiled::NoArgs,
                ParameterP::Args(x, t) => ParameterCompiled::Args(
                    self.parameter_name(x),
                    self.expr_opt(t).map(ExprCompiledValue::as_compiled),
                ),
                ParameterP::KwArgs(x, t) => ParameterCompiled::KwArgs(
                    self.parameter_name(x),
                    self.expr_opt(t).map(ExprCompiledValue::as_compiled),
                ),
            },
        }
    }

    /// If a statement is `return type(x) == "y"` where `x` is a first slot.
    fn is_return_type_is(stmt: &StmtsCompiled) -> Option<FrozenStringValue> {
        match stmt.first() {
            Some(StmtCompiledValue::Return(
                _,
                Some(ExprCompiledValue::TypeIs(
                    // Slot 0 is a slot for the first function argument.
                    box ExprCompiledValue::Local(LocalSlotId(0), ..),
                    t,
                    MaybeNot::Id,
                )),
            )) => Some(*t),
            _ => None,
        }
    }

    pub fn function(
        &mut self,
        name: &str,
        scope_id: ScopeId,
        params: Vec<CstParameter>,
        return_type: Option<Box<CstExpr>>,
        suite: CstStmt,
    ) -> ExprCompiledValue {
        let file = self.codemap.file_span(suite.span);
        let function_name = format!("{}.{}", file.file.filename(), name);

        // The parameters run in the scope of the parent, so compile them with the outer
        // scope
        let params = params.into_map(|x| self.parameter(x));
        let return_type = return_type.map(|return_type| Spanned {
            span: return_type.span,
            node: self.expr(*return_type).as_compiled(),
        });

        self.enter_scope(scope_id);

        let docstring = DocString::extract_raw_starlark_docstring(&suite);
        let body = self.stmt(suite, false);
        let scope_names = self.exit_scope();

        let scope_names = mem::take(scope_names);

        let returns_type_is = if params.len() == 1 && params[0].accepts_positional() {
            Self::is_return_type_is(&body)
        } else {
            None
        };

        let info = Arc::new(DefInfo {
            scope_names,
            body: body.as_compiled(self),
            returns_type_is,
        });

        expr!("def", |eval| {
            let mut parameters =
                ParametersSpec::with_capacity(function_name.to_owned(), params.len());
            let mut parameter_types = Vec::new();
            let mut parameter_captures = Vec::new();

            // count here rather than enumerate because '*' doesn't get a real
            // index in the parameter mapping, and it messes up the indexes
            let mut i = 0;
            for x in params.iter() {
                if let Some(t) = x.ty() {
                    let v = t(eval)?;
                    let name = x.name().unwrap_or("unknown").to_owned();
                    parameter_types.push((
                        i,
                        name,
                        v,
                        expr_throw(TypeCompiled::new(v, eval.heap()), x.span, eval)?,
                    ));
                }
                match &x.node {
                    ParameterCompiled::Normal(n, _) => parameters.required(&n.name),
                    ParameterCompiled::WithDefaultValue(n, _, v) => {
                        parameters.defaulted(&n.name, v(eval)?)
                    }
                    ParameterCompiled::NoArgs => parameters.no_args(),
                    ParameterCompiled::Args(_, _) => parameters.args(),
                    ParameterCompiled::KwArgs(_, _) => parameters.kwargs(),
                };
                if let Captured::Yes = x.captured() {
                    parameter_captures.push(i);
                }
                if !matches!(x.node, ParameterCompiled::NoArgs) {
                    i += 1;
                }
            }
            let return_type = match &return_type {
                None => None,
                Some(v) => {
                    let value = (v.node)(eval)?;
                    Some((
                        value,
                        expr_throw(TypeCompiled::new(value, eval.heap()), v.span, eval)?,
                    ))
                }
            };
            Def::new(
                parameters,
                parameter_captures,
                parameter_types,
                return_type,
                info.dupe(),
                eval,
                docstring.clone(),
            )
        })
    }
}

/// Starlark function internal representation and implementation of
/// [`StarlarkValue`].
#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct DefGen<V> {
    parameters: ParametersSpec<V>, // The parameters, **kwargs etc including defaults (which are evaluated afresh each time)
    parameter_captures: Vec<usize>, // Indices of parameters, which are captured in nested defs
    parameter_types: Vec<(usize, String, V, TypeCompiled)>, // The types of the parameters (sparse indexed array, (0, argm T) implies parameter 0 named arg must have type T)
    return_type: Option<(V, TypeCompiled)>, // The return type annotation for the function
    codemap: CodeMap,                       // Codemap that was active during this module
    pub(crate) stmt: Arc<DefInfo>,          // The source code and metadata for this function
    /// Any variables captured from the outer scope (nested def/lambda).
    /// Values are either [`Value`] or [`FrozenValu`] pointing respectively to
    /// [`ValueCaptured`] or [`FrozenValueCaptured`].
    captured: Vec<V>,
    // Important to ignore these field as it probably references DefGen in a cycle
    #[derivative(Debug = "ignore")]
    module: Option<FrozenModuleValue>, // A reference to the module variables, if we have been frozen
    docstring: Option<String>, // The raw docstring pulled out of the AST
}

pub(crate) type Def<'v> = DefGen<Value<'v>>;
pub(crate) type FrozenDef = DefGen<FrozenValue>;

starlark_complex_values!(Def);

impl<'v> Def<'v> {
    fn new(
        parameters: ParametersSpec<Value<'v>>,
        parameter_captures: Vec<usize>,
        parameter_types: Vec<(usize, String, Value<'v>, TypeCompiled)>,
        return_type: Option<(Value<'v>, TypeCompiled)>,
        stmt: Arc<DefInfo>,
        eval: &mut Evaluator<'v, '_>,
        docstring: Option<String>,
    ) -> Value<'v> {
        let captured = stmt
            .scope_names
            .parent
            .map(|(x, _)| eval.clone_slot_capture(*x));
        eval.heap().alloc(Self {
            parameters,
            parameter_captures,
            parameter_types,
            return_type,
            stmt,
            codemap: eval.codemap.dupe(),
            captured,
            module: eval.module_variables.map(|x| x.1),
            docstring,
        })
    }
}

impl<'v, T1: ValueLike<'v>> DefGen<T1> {
    /// Extract a few key things out of the main function docstring
    fn parse_docstring(
        &self,
    ) -> (
        Option<DocString>,
        HashMap<String, Option<DocString>>,
        Option<DocString>,
    ) {
        let docstring = self
            .docstring
            .as_ref()
            .and_then(|s| DocString::from_docstring(s));
        let mut param_docs = HashMap::new();
        let mut return_docs = None;

        if let Some(ds) = &docstring {
            let sections = ds.parse_sections();
            if let Some(args) = sections.get("args") {
                param_docs = DocString::parse_params(args)
                    .into_iter()
                    .map(|(name, docs)| (name, DocString::from_docstring(&docs)))
                    .collect();
            }
            if let Some(docs) = sections.get("returns") {
                return_docs = DocString::from_docstring(docs);
            }
        };
        (docstring, param_docs, return_docs)
    }

    fn docs(&self) -> Option<DocItem> {
        let (def_docstring, parameter_docs, return_docs) = self.parse_docstring();

        let parameter_types: HashMap<usize, docs::Type> = self
            .parameter_types
            .iter()
            .map(|(idx, _, v, _)| {
                (
                    *idx,
                    docs::Type {
                        raw_type: v.to_value().to_repr(),
                    },
                )
            })
            .collect();

        let mut parameters: Vec<docs::Param> = self
            .parameters
            .iter_params()
            .map(|(i, name, kind)| {
                let typ = parameter_types.get(&i).cloned();
                let docs = parameter_docs.get(name).and_then(|x| x.clone());
                let name = name.to_owned();
                match kind {
                    ParameterKind::Required => docs::Param::Arg {
                        name,
                        docs,
                        typ,
                        default_value: None,
                    },
                    ParameterKind::Optional => docs::Param::Arg {
                        name,
                        docs,
                        typ,
                        default_value: Some("None".to_owned()),
                    },
                    ParameterKind::Defaulted(v) => docs::Param::Arg {
                        name,
                        docs,
                        typ,
                        default_value: Some(v.to_value().to_repr()),
                    },
                    ParameterKind::Args => docs::Param::Args { name, docs, typ },
                    ParameterKind::KWargs => docs::Param::Kwargs { name, docs, typ },
                }
            })
            .collect();

        // Go back and add the "*" arg if it's present
        if let Some(i) = self.parameters.no_args_param_index() {
            parameters.insert(i, docs::Param::NoArgs);
        }

        let return_details = docs::Return {
            docs: return_docs,
            typ: self.return_type.as_ref().map(|r| docs::Type {
                raw_type: r.0.to_value().to_repr(),
            }),
        };

        Some(DocItem::Function(docs::Function {
            docs: def_docstring,
            params: parameters,
            ret: return_details,
        }))
    }
}

impl<T1> DefGen<T1> {
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
        let module = Some(
            self.module
                .unwrap_or_else(|| FrozenModuleValue::new(freezer)),
        );
        Ok(FrozenDef {
            parameters,
            parameter_captures: self.parameter_captures,
            parameter_types,
            return_type,
            codemap: self.codemap,
            stmt: self.stmt,
            captured,
            module,
            docstring: self.docstring,
        })
    }
}

impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for DefGen<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(FUNCTION_TYPE);

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str(&self.parameters.signature());
    }

    fn invoke(
        &self,
        me: Value<'v>,
        location: Option<Span>,
        args: Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_>,
    ) -> anyhow::Result<Value<'v>> {
        eval.ann("invoke_def", |eval| {
            let local_slots = self.stmt.scope_names.used;
            let slot_base = eval.local_variables.reserve(local_slots);
            let slots = eval.local_variables.get_slots_at(slot_base);
            self.parameters.collect_inline(args, slots, eval.heap())?;
            eval.with_call_stack(me, location, |eval| {
                eval.ann("invoke_def_raw", |eval| self.invoke_raw(slot_base, eval))
            })
        })
    }

    fn documentation(&self) -> Option<DocItem> {
        self.docs()
    }
}

impl<'v, V: ValueLike<'v>> DefGen<V> {
    fn invoke_raw(
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

        // Parameters are collected into local slots without captures
        // (to avoid even more branches in parameter capture),
        // and this loop wraps captured parameters.
        for &captured in &self.parameter_captures {
            eval.wrap_local_slot_captured(LocalSlotId::new(captured));
        }

        // Copy over the parent slots
        for ((_, me), captured) in self
            .stmt
            .scope_names
            .parent
            .iter()
            .zip(self.captured.iter())
        {
            eval.local_variables.set_slot(*me, captured.to_value());
        }

        let res =
            eval.with_function_context(self.module, &self.codemap, |eval| (self.stmt.body)(eval));
        eval.local_variables.release(old_locals);

        let ret = match res {
            Err(EvalException::Return(ret)) => ret,
            Err(e) => return throw_eval_exception(e),
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
