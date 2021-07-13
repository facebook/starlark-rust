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
    parse_macro_input, parse_quote, spanned::Spanned, Data, DataStruct, DeriveInput, Fields,
    GenericParam, Lifetime, LifetimeDef, TypeParamBound,
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

fn trace_struct(data: &DataStruct) -> TokenStream {
    match data.fields {
        Fields::Named(ref fields) => {
            let xs: Vec<_> = fields
                .named
                .iter()
                .map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span() =>
                        self.#name.trace(tracer);
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
                .map(|(i, f)| {
                    let i = syn::Index::from(i);
                    quote_spanned! {f.span() => self.#i.trace(tracer);}
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

fn trace_impl(data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => trace_struct(data),
        Data::Enum(_) => unimplemented!("Can't derive Trace for enums"),
        Data::Union(_) => unimplemented!("Can't derive Trace for unions"),
    }
}
