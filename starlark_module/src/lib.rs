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

//! A proc-macro for writing functions in Rust that can be called from Starlark.

#![feature(box_patterns)]

#[allow(unused_extern_crates)] // proc_macro is very special
extern crate proc_macro;

use gazebo::prelude::*;
use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::*;

// The output for the example below should be:
//
// ```
// pub fn global(globals_builder: &mut GlobalsBuilder) {
//     fn cc_binary<'v, 'a, 'a2>(
//         ctx: &mut starlark::eval::Evaluator<'v, 'a>,
//         args: starlark::eval::ParametersParser<'v, 'a2>,
//     ) -> anyhow::Result<starlark::values::Value<'v>> {
//         fn inner<'v, 'a, 'a2>(
//             #[allow(unused_variables)] ctx: &mut starlark::eval::Evaluator<'v, 'a>,
//             #[allow(unused_mut)]
//             #[allow(unused_variables)]
//             mut args: starlark::eval::ParametersParser<'v, 'a2>,
//         ) -> anyhow::Result<String> {
//             #[allow(unused_mut)]
//             let mut name: &str = args.next("name", ctx.heap())?;
//             #[allow(unused_mut)]
//             let mut srcs: Vec<&str> = args.next("srcs", ctx.heap())?;
//             Ok({
//                 let res = ::alloc::fmt::format(::core::fmt::Arguments::new_v1(
//                     &["", " "],
//                     &match (&name, &srcs) {
//                         (arg0, arg1) => [
//                             ::core::fmt::ArgumentV1::new(arg0, ::core::fmt::Debug::fmt),
//                             ::core::fmt::ArgumentV1::new(arg1, ::core::fmt::Debug::fmt),
//                         ],
//                     },
//                 ));
//                 res
//             })
//         }
//         match inner(ctx, args) {
//             Ok(v) => Ok(ctx.heap().alloc(v)),
//             Err(e) => Err(e),
//         }
//     }
//     {
//         #[allow(unused_mut)]
//         let mut signature = starlark::eval::ParametersSpec::with_capcity("cc_binary".to_owned(), 2);
//         signature.required("name");
//         signature.required("srcs");
//         globals_builder.set(
//             name,
//             starlark::values::function::NativeFunction::new(cc_binary, signature),
//         );
//     }
//     globals_builder
// }
// ```

/// Write Starlark modules concisely in Rust syntax.
///
/// For example:
///
/// ```ignore
/// #[starlark_module]
/// fn global(registry: &mut GlobalsBuilder) {
///     fn cc_binary(name: &str, srcs: Vec<&str>) -> String {
///         Ok(format!("{:?} {:?}", name, srcs))
///     }
/// }
/// ```
///
/// Parameters operate as named parameters of a given type, with five possible tweaks:
///
/// * `args` means the argument is the `*args`.
/// * `kwargs` means the argument is the `**kwargs`.
/// * `ref name` means the argument must be passed by position, not by name.
/// * A type of `Option` means the argument is optional.
/// * A pattern `x @ foo : bool` means the argument defaults to `foo` if not
///   specified.
///
/// During execution there are two local variables injected into scope:
///
/// * `ctx` is the `Evaluator`.
/// * `heap` is the `Heap`, obtained from `ctx.heap()`.
///
/// A function with the `#[starlark_module]` attribute can be added to a `GlobalsBuilder` value
/// using the `with` function. Those `Globals` can be passed to `Evaluator` to provide global functions.
/// Alternatively, you can return `Globals` from `get_methods` to _attach_ functions to
/// a specific type (e.g. the `string` type).
///
/// * When unattached, you can define constants with `const`. We define `True`, `False` and
///   `None` that way.
/// * When attached, you can annotate the functions with `#[attribute]` to turn the name into
///   an attribute on the value. Such a function must take exactly one argument, namely a value
///   of the type you have attached it to.
/// * The attribute `#[starlark_type("test")]` causes `f.type` to return `"test"`.
///
/// All these functions interoperate properly with `dir()`, `getattr()` and `hasattr()`.
///
/// If a desired function name is also a Rust keyword, use the `r#` prefix, e.g. `r#type`.
#[proc_macro_attribute]
pub fn starlark_module(attr: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as ItemFn);
    assert!(attr.is_empty());

    let visibility = input.vis;
    let name = input.sig.ident;
    let arg_ty = match input.sig.inputs.first() {
        Some(FnArg::Typed(PatType { ty, .. })) if is_mut_globals_builder(ty) => ty,
        _ => panic!("Must take on argument of type &mut GlobalsBuilder"),
    };
    let body = input.block.stmts.map(add_stmt);
    let result = quote! {
        #visibility fn #name(globals_builder: #arg_ty) {
            #( #body )*
        }
    };
    result.into()
}

#[derive(Clone)]
struct Arg<'a> {
    attrs: &'a Vec<Attribute>,
    ident: &'a PatIdent,
    ty: &'a Type,
}

impl<'a> Arg<'a> {
    fn new(x: &'a FnArg) -> Self {
        match x {
            FnArg::Typed(PatType {
                attrs,
                pat: box Pat::Ident(ident),
                ty: box ty,
                ..
            }) => Self { attrs, ident, ty },
            arg => panic!("Unexpected argument, {:?}", arg),
        }
    }
}

fn add_stmt(stmt: &Stmt) -> proc_macro2::TokenStream {
    match stmt {
        Stmt::Item(Item::Fn(x)) => add_function(x),
        Stmt::Item(Item::Const(x)) => add_const(x),
        _ => panic!("Can only put constants and functions inside a #[starlark_module]"),
    }
}

fn add_const(x: &ItemConst) -> proc_macro2::TokenStream {
    let name_str = x.ident.to_string();
    let ty = &x.ty;
    let value = &x.expr;
    quote! {
        globals_builder.set::<#ty>(#name_str, #value);
    }
}

fn is_attribute_attribute(x: &Attribute) -> bool {
    x.path.is_ident("attribute")
}

fn is_attribute_type(x: &Attribute) -> Option<impl ToTokens> {
    if x.path.is_ident("starlark_type") {
        if let Ok(Meta::List(MetaList { nested, .. })) = x.parse_meta() {
            if nested.len() == 1 {
                return Some(nested.first().unwrap().clone());
            }
        }
        panic!(
            "Couldn't parse attribute `{:?}`. Expected `#[starlark_type(\"my_type\")]`",
            x
        )
    } else {
        None
    }
}

/// (#[attribute], #[starlark_type(x)], rest)
fn process_attributes(xs: &[Attribute]) -> (bool, Option<impl ToTokens>, Vec<&Attribute>) {
    let mut rest = Vec::with_capacity(xs.len());
    let mut attribute = false;
    let mut typ = None;
    for x in xs {
        if is_attribute_attribute(x) {
            attribute = true;
        } else if let Some(t) = is_attribute_type(x) {
            typ = Some(t);
        } else {
            rest.push(x);
        }
    }
    (attribute, typ, rest)
}

// Add a function to the `GlobalsModule` named `globals_builder`.
fn add_function(func: &ItemFn) -> proc_macro2::TokenStream {
    let name = &func.sig.ident;
    let name_string = name.to_string();
    let name_str = name_string.trim_start_match("r#");
    let (is_attribute, has_type, attrs) = process_attributes(&func.attrs);

    let return_type = match &func.sig.output {
        ReturnType::Default => panic!("Function named '{}' must have a return type", name),
        ReturnType::Type(_, x) => quote! {#x},
    };
    let body = &func.block;
    let args = func.sig.inputs.iter().map(Arg::new).collect::<Vec<_>>();
    let args_count = args.len();
    let bind_args = args.map(bind_argument);
    let signature = args.map(record_argument);
    let setter = if is_attribute {
        quote! {
            let func = globals_builder.alloc(
                starlark::values::function::NativeFunction::new(#name, signature),
            );
            globals_builder.set(
                #name_str,
                starlark::values::function::NativeAttribute::new(func),
            );
        }
    } else if let Some(typ) = has_type {
        quote! {
            static TYPE: starlark::values::ConstFrozenValue =
                starlark::values::ConstFrozenValue::new(#typ);
            let mut func = starlark::values::function::NativeFunction::new(#name, signature);
            func.set_type(&TYPE);
            globals_builder.set(#name_str, func);
        }
    } else {
        quote! {
            globals_builder.set(
                #name_str,
                starlark::values::function::NativeFunction::new(#name, signature),
            );
        }
    };
    quote! {
        #( #attrs )*
        #[allow(non_snake_case)] // Starlark doesn't have this convention
        fn #name<'v, 'a, 'a2>(
            ctx: &mut starlark::eval::Evaluator<'v, 'a>,
            starlark_args: starlark::eval::ParametersParser<'v, 'a2>,
        ) -> anyhow::Result<starlark::values::Value<'v>> {
             fn inner<'v, 'a, 'a2>(
                #[allow(unused_variables)]
                ctx: &mut starlark::eval::Evaluator<'v, 'a>,
                #[allow(unused_mut)]
                #[allow(unused_variables)]
                mut starlark_args: starlark::eval::ParametersParser<'v, 'a2>,
            ) -> anyhow::Result<#return_type> {
                #[allow(unused_variables)]
                let heap = ctx.heap();
                #( #bind_args )*
                #body
            }
            match inner(ctx, starlark_args) {
                Ok(v) => Ok(ctx.heap().alloc(v)),
                Err(e) => Err(e),
            }
        }
        {
            #[allow(unused_mut)]
            let mut signature = starlark::eval::ParametersSpec::with_capacity(#name_str.to_owned(), #args_count);
            #( #signature )*
            #setter
        }
    }
}

fn bind_argument(arg: &Arg) -> proc_macro2::TokenStream {
    let name = &arg.ident.ident;
    let name_str = name.to_string();
    let ty = arg.ty;
    let default = get_default(arg);

    let next = if is_type_option(ty) {
        assert!(
            default.is_none(),
            "Can't have Option argument with a default, for `{}`",
            name_str
        );
        quote! { starlark_args.next_opt(#name_str, ctx.heap())? }
    } else if !is_type_value(ty) && default.is_some() {
        let default = default.unwrap();
        quote! { starlark_args.next_opt(#name_str, ctx.heap())?.unwrap_or(#default) }
    } else {
        quote! { starlark_args.next(#name_str, ctx.heap())? }
    };

    let mutability = &arg.ident.mutability;
    let attrs = &arg.attrs;
    quote! {
        #( #attrs )*
        let #mutability #name: #ty = #next;
    }
}

fn record_argument(arg: &Arg) -> proc_macro2::TokenStream {
    let name = &arg.ident.ident;
    let mut name_str_full = (if arg.ident.by_ref.is_some() { "$" } else { "" }).to_owned();
    name_str_full += &name.to_string();
    let name_str = name_str_full.trim_matches('_');
    let default = get_default(arg);
    match name_str_full.as_str() {
        "args" => {
            assert!(default.is_none(), "Can't have *args with a default");
            quote! {signature.args();}
        }
        "kwargs" => {
            assert!(default.is_none(), "Can't have **kwargs with a default");
            quote! {signature.kwargs();}
        }
        _ if is_type_option(arg.ty) => {
            quote! {signature.optional(#name_str);}
        }
        _ if default.is_some() => {
            let default = default.unwrap();
            let ty = arg.ty;
            // For things that are type Value, we put them on the frozen heap.
            // For things that aren't type value, use optional and then next_opt/unwrap
            // to avoid the to/from value conversion.
            if is_type_value(ty) {
                quote! {signature.defaulted(#name_str, globals_builder.alloc(#default));}
            } else {
                quote! {signature.optional(#name_str);}
            }
        }
        _ => {
            quote! {signature.required(#name_str);}
        }
    }
}

// Is a type matching a given name
fn is_type_name(x: &Type, name: &str) -> bool {
    if let Type::Path(TypePath {
        path: Path { segments, .. },
        ..
    }) = x
    {
        if let Some(seg1) = segments.first() {
            return seg1.ident == name;
        }
    }
    false
}

// Get the default value, specified with `name @ default : type`
fn get_default<'a>(arg: &'a Arg) -> Option<&'a Pat> {
    arg.ident.subpat.as_ref().map(|(_, x)| &**x)
}

// Is the type `Option<foo>`
fn is_type_option(x: &Type) -> bool {
    is_type_name(x, "Option")
}

// Is the type `Value`
fn is_type_value(x: &Type) -> bool {
    is_type_name(x, "Value")
}

// Is the type `&mut GlobalsBuilder`
fn is_mut_globals_builder(x: &Type) -> bool {
    match x {
        Type::Reference(TypeReference {
            mutability: Some(_),
            elem: x,
            ..
        }) => is_type_name(x, "GlobalsBuilder"),
        _ => false,
    }
}
