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

use crate::{typ::*, util::*};
use gazebo::prelude::*;
use proc_macro2::TokenStream;
use quote::quote;

pub(crate) fn render(x: StarModule) -> TokenStream {
    let StarModule {
        name,
        globals_builder,
        visibility,
        stmts,
    } = x;
    let stmts = stmts.into_map(render_stmt);
    quote! {
        #visibility fn #name(globals_builder: #globals_builder) {
            fn build(globals_builder: &mut starlark::environment::GlobalsBuilder) {
                #( #stmts )*
            }
            static RES: starlark::environment::GlobalsStatic = starlark::environment::GlobalsStatic::new();
            RES.populate(build, globals_builder);
        }
    }
}

fn render_stmt(x: StarStmt) -> TokenStream {
    match x {
        StarStmt::Const(x) => render_const(x),
        StarStmt::Attr(x) => render_attr(x),
        StarStmt::Fun(x) => render_fun(x),
    }
}

fn render_const(x: StarConst) -> TokenStream {
    let StarConst { name, ty, value } = x;
    let name = ident_string(&name);
    quote! {
        globals_builder.set::<#ty>(#name, #value);
    }
}

fn render_attr(x: StarAttr) -> TokenStream {
    let StarAttr {
        name,
        arg,
        attrs,
        return_type,
        body,
    } = x;
    let name_str = ident_string(&name);
    quote! {
        #( #attrs )*
        #[allow(non_snake_case)] // Starlark doesn't have this convention
        fn #name<'v, 'a>(
            #[allow(unused_variables)]
            this: starlark::values::Value<'v>,
            eval: &mut starlark::eval::Evaluator<'v, 'a>,
        ) -> anyhow::Result<starlark::values::Value<'v>> {
             fn inner<'v, 'a>(
                this: Value<'v>,
                #[allow(unused_variables)]
                eval: &mut starlark::eval::Evaluator<'v, 'a>,
            ) -> anyhow::Result<#return_type> {
                #[allow(unused_variables)]
                let heap = eval.heap();
                #[allow(unused_variables)]
                let this: #arg = match starlark::values::UnpackValue::unpack_value(this) {
                    None => return Err(starlark::values::ValueError::IncorrectParameterTypeNamed("this".to_owned()).into()),
                    Some(v) => v,
                };
                #body
            }
            Ok(eval.heap().alloc(inner(this, eval)?))
        }
        globals_builder.set(
            #name_str,
            starlark::values::function::NativeAttribute::new(#name),
        );
    }
}

fn render_fun(x: StarFun) -> TokenStream {
    let name_str = ident_string(&x.name);
    let native_name_str = format!("native_{}", name_str);
    let signature = render_signature(&x);
    let is_parameters = x.is_parameters();

    let StarFun {
        name,
        type_attribute,
        attrs,
        args,
        return_type,
        body,
    } = x;

    let set_type = if let Some(typ) = type_attribute {
        quote! {
            static TYPE: starlark::values::ConstFrozenValue =
                starlark::values::ConstFrozenValue::new(#typ);
            func.set_type(&TYPE);
        }
    } else {
        quote! {}
    };

    if is_parameters {
        let param_name = &args[0].name;
        let param_type = &args[0].ty;
        quote! {
            #( #attrs )*
            #[allow(non_snake_case)] // Starlark doesn't have this convention
            fn #name<'v>(
                eval: &mut starlark::eval::Evaluator<'v, '_>,
                #[allow(unused_variables)]
                parameters: starlark::eval::Parameters<'v, '_>,
            ) -> anyhow::Result<starlark::values::Value<'v>> {
                 fn inner<'v, 'a>(
                    #[allow(unused_variables)]
                    eval: &mut starlark::eval::Evaluator<'v, '_>,
                    #[allow(unused_variables)]
                    #param_name: #param_type,
                ) -> anyhow::Result<#return_type> {
                    let heap = eval.heap();
                    eval.ann(#native_name_str, |eval| {
                        #body
                    })
                }
                match inner(eval, parameters) {
                    Ok(v) => Ok(eval.heap().alloc(v)),
                    Err(e) => Err(e),
                }
            }
            {
                #[allow(unused_mut)]
                let mut func = starlark::values::function::NativeFunction::new_direct(#name, #name_str.to_owned());
                #set_type
                globals_builder.set(#name_str, func);
            }
        }
    } else {
        let bind_args = args.map(bind_argument);

        quote! {
            #( #attrs )*
            #[allow(non_snake_case)] // Starlark doesn't have this convention
            fn #name<'v>(
                eval: &mut starlark::eval::Evaluator<'v, '_>,
                #[allow(unused_variables)]
                this: Option<starlark::values::Value<'v>>,
                starlark_args: starlark::eval::ParametersParser<'v, '_>,
            ) -> anyhow::Result<starlark::values::Value<'v>> {
                 fn inner<'v>(
                    #[allow(unused_variables)]
                    eval: &mut starlark::eval::Evaluator<'v, '_>,
                    #[allow(unused_variables)]
                    this: Option<starlark::values::Value<'v>>,
                    #[allow(unused_mut)]
                    #[allow(unused_variables)]
                    mut starlark_args: starlark::eval::ParametersParser<'v, '_>,
                ) -> anyhow::Result<#return_type> {
                    #[allow(unused_variables)]
                    let heap = eval.heap();
                    eval.ann(#native_name_str, |eval| {
                        #( #bind_args )*
                        #body
                    })
                }
                match inner(eval, this, starlark_args) {
                    Ok(v) => Ok(eval.heap().alloc(v)),
                    Err(e) => Err(e),
                }
            }
            {
                #signature
                let signature_str = signature.signature();
                #[allow(unused_mut)]
                let mut func = starlark::values::function::NativeFunction::new(#name, signature_str, signature);
                #set_type
                globals_builder.set(#name_str, func);
            }
        }
    }
}

// Create a binding for an argument given
fn bind_argument(arg: &StarArg) -> TokenStream {
    let name = &arg.name;
    let name_str = ident_string(name);
    let ty = &arg.ty;

    // Rust doesn't have powerful enough nested if yet
    let next = if arg.is_this() {
        quote! { starlark_args.this(this)? }
    } else if arg.is_option() {
        assert!(
            arg.default.is_none(),
            "Can't have Option argument with a default, for `{}`",
            name_str
        );
        quote! { starlark_args.next_opt(#name_str)? }
    } else if !arg.is_value() && arg.default.is_some() {
        let default = arg
            .default
            .as_ref()
            .unwrap_or_else(|| unreachable!("Checked on the line above"));
        quote! { starlark_args.next_opt(#name_str)?.unwrap_or(#default) }
    } else {
        quote! { starlark_args.next(#name_str)? }
    };

    let mutability = mut_token(arg.mutable);
    let attrs = &arg.attrs;
    quote! {
        #( #attrs )*
        let #mutability #name: #ty = #next;
    }
}

// Given the arguments, create a variable `signature` with a `ParametersSpec` object.
fn render_signature(x: &StarFun) -> TokenStream {
    let name_str = ident_string(&x.name);
    let args_count = x.args.len();
    let sig_args = x.args.map(render_signature_arg);
    quote! {
        #[allow(unused_mut)]
        let mut signature = starlark::eval::ParametersSpecBuilder::with_capacity(#name_str.to_owned(), #args_count);
        #( #sig_args )*
        let signature = signature.build();
    }
}

// Generate a statement that modifies signature to add a new argument in.
fn render_signature_arg(arg: &StarArg) -> TokenStream {
    let mut name_str_full = (if arg.by_ref { "$" } else { "" }).to_owned();
    name_str_full += &ident_string(&arg.name);
    let name_str = name_str_full.trim_matches('_');

    if arg.is_args() {
        assert!(arg.default.is_none(), "Can't have *args with a default");
        quote! {signature.args();}
    } else if arg.is_kwargs() {
        assert!(arg.default.is_none(), "Can't have **kwargs with a default");
        quote! {signature.kwargs();}
    } else if arg.is_this() {
        quote! {}
    } else if arg.is_option() {
        quote! {signature.optional(#name_str);}
    } else if let Some(default) = &arg.default {
        // For things that are type Value, we put them on the frozen heap.
        // For things that aren't type value, use optional and then next_opt/unwrap
        // to avoid the to/from value conversion.
        if arg.is_value() {
            quote! {signature.defaulted(#name_str, globals_builder.alloc(#default));}
        } else {
            quote! {signature.optional(#name_str);}
        }
    } else {
        quote! {signature.required(#name_str);}
    }
}
