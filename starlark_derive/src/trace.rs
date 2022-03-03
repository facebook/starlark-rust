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

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    parse::ParseStream, parse_macro_input, parse_quote, spanned::Spanned, Attribute, Data,
    DataEnum, DataStruct, DeriveInput, Fields, GenericParam, Lifetime, LifetimeDef, TypeParamBound,
};

pub fn derive_trace(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let mut input = parse_macro_input!(input as DeriveInput);
    let tick_v = GenericParam::Lifetime(LifetimeDef::new(Lifetime::new("'v", Span::call_site())));

    let bound: TypeParamBound = parse_quote!(starlark::values::Trace<'v>);
    let mut has_tick_v = false;
    for param in &mut input.generics.params {
        if let GenericParam::Type(type_param) = param {
            type_param.bounds.push(bound.clone());
        }
        if let GenericParam::Lifetime(t) = param {
            if t.lifetime.ident == "v" {
                has_tick_v = true;
            }
        }
    }
    let mut generics2 = input.generics.clone();

    let (_, ty_generics, where_clause) = input.generics.split_for_impl();
    if !has_tick_v {
        generics2.params.insert(0, tick_v);
    }
    let (impl_generics, _, _) = generics2.split_for_impl();

    let name = &input.ident;
    let body = trace_impl(&input.data);
    let gen = quote! {
        unsafe impl #impl_generics starlark::values::Trace<'v> for #name #ty_generics #where_clause {
            fn trace(&mut self, tracer: &starlark::values::Tracer<'v>) {
                #body
            }
        }
    };
    gen.into()
}

/// Parse attribute `#[trace(unsafe_ignore)]`.
///
/// Currently it fails on any attribute argument other than `unsafe_ignore`.
#[cfg_attr(feature = "gazebo_lint", allow(gazebo_lint_impl_dupe))] // The custom_keyword macro
fn is_ignore(attrs: &[Attribute]) -> bool {
    syn::custom_keyword!(unsafe_ignore);

    attrs.iter().any(|a| {
        a.path.is_ident("trace")
            && a.parse_args_with(|input: ParseStream| {
                let ignore = input.parse::<Option<unsafe_ignore>>()?.is_some();
                Ok(ignore)
            })
            .unwrap()
    })
}

fn trace_struct(data: &DataStruct) -> TokenStream {
    match data.fields {
        Fields::Named(ref fields) => {
            let xs: Vec<_> = fields
                .named
                .iter()
                .filter_map(|f| {
                    if !is_ignore(&f.attrs) {
                        let name = &f.ident;
                        Some(quote_spanned! {f.span() =>
                            starlark::values::Trace::trace(&mut self.#name, tracer);
                        })
                    } else {
                        None
                    }
                })
                .collect();
            quote! {
                #(#xs)*
            }
        }
        Fields::Unnamed(ref fields) => {
            let xs: Vec<_> = fields
                .unnamed
                .iter()
                .enumerate()
                .filter_map(|(i, f)| {
                    if !is_ignore(&f.attrs) {
                        let i = syn::Index::from(i);
                        Some(quote_spanned! {f.span() => starlark::values::Trace::trace(&mut self.#i, tracer);})
                    } else {
                        None
                    }
                })
                .collect();
            quote! {
                #(#xs)*
            }
        }
        Fields::Unit => {
            quote!()
        }
    }
}

fn trace_enum(data: &DataEnum) -> TokenStream {
    for variant in &data.variants {
        if let Fields::Unit = variant.fields {
            continue;
        }
        match &variant.fields {
            Fields::Named(fields) => {
                for field in &fields.named {
                    if is_ignore(&field.attrs) {
                        continue;
                    }
                    // TODO: implement
                    unimplemented!("Can't derive Trace for enums");
                }
            }
            Fields::Unnamed(fields) => {
                for field in &fields.unnamed {
                    if is_ignore(&field.attrs) {
                        continue;
                    }
                    // TODO: implement
                    unimplemented!("Can't derive Trace for enums");
                }
            }
            Fields::Unit => {}
        }
    }
    quote!()
}

fn trace_impl(data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => trace_struct(data),
        Data::Enum(data) => trace_enum(data),
        Data::Union(_) => unimplemented!("Can't derive Trace for unions"),
    }
}
