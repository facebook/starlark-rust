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

//! Derive macros for `StarlarkSerialize` and `StarlarkDeserialize`.
//!
//! By default, each field is serialized/deserialized through the starlark context
//! (`StarlarkSerialize::starlark_serialize` / `StarlarkDeserialize::starlark_deserialize`).
//!
//! Fields annotated with `#[starlark_pagable(pagable)]` use the pagable bridge instead
//! (`PagableSerialize::pagable_serialize(ctx.pagable())` /
//!  `PagableDeserialize::pagable_deserialize(ctx.pagable())`).

use proc_macro2::Ident;
use quote::quote;
use quote::quote_spanned;
use syn::Attribute;
use syn::DeriveInput;
use syn::Fields;
use syn::Index;
use syn::parse::ParseStream;
use syn::parse_macro_input;
use syn::spanned::Spanned;

#[derive(Default)]
struct FieldAttrs {
    pagable: bool,
}

fn extract_field_attrs(attrs: &[Attribute]) -> syn::Result<FieldAttrs> {
    syn::custom_keyword!(pagable);

    let mut opts = FieldAttrs::default();

    for attr in attrs {
        if !attr.path().is_ident("starlark_pagable") {
            continue;
        }

        attr.parse_args_with(|input: ParseStream| {
            if input.parse::<pagable>().is_ok() {
                if opts.pagable {
                    return Err(input.error("`pagable` was set twice"));
                }
                opts.pagable = true;
            }
            if !input.is_empty() {
                return Err(input.error(format!(
                    "invalid attribute `{}`, expected `pagable` in `#[starlark_pagable(...)]`",
                    input
                )));
            }
            Ok(())
        })?;
    }

    Ok(opts)
}

fn field_ident(i: usize, field: &syn::Field) -> proc_macro2::TokenStream {
    match &field.ident {
        Some(name) => quote! { #name },
        None => {
            let idx = Index::from(i);
            quote! { #idx }
        }
    }
}

pub fn derive_starlark_pagable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let ser = derive_starlark_serialize_impl(&input);
    let de = derive_starlark_deserialize_impl(&input);
    match (ser, de) {
        (Ok(ser), Ok(de)) => quote! { #ser #de }.into(),
        (Err(err), _) | (_, Err(err)) => err.to_compile_error().into(),
    }
}

pub fn derive_starlark_serialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_starlark_serialize_impl(&input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn derive_starlark_serialize_impl(input: &DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let body = match &input.data {
        syn::Data::Struct(data) => gen_serialize_fields(&data.fields)?,
        syn::Data::Enum(_) => {
            return Err(syn::Error::new_spanned(
                input,
                "StarlarkSerialize derive does not support enums",
            ));
        }
        syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                input,
                "StarlarkSerialize derive does not support unions",
            ));
        }
    };

    Ok(quote! {
        impl #impl_generics starlark::pagable::StarlarkSerialize for #name #ty_generics #where_clause {
            fn starlark_serialize(
                &self,
                ctx: &mut dyn starlark::pagable::StarlarkSerializeContext,
            ) -> starlark::Result<()> {
                #body
                Ok(())
            }
        }
    })
}

fn gen_serialize_fields(fields: &Fields) -> syn::Result<proc_macro2::TokenStream> {
    let mut stmts = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let attrs = extract_field_attrs(&field.attrs)?;
        let ident = field_ident(i, field);
        let ty = &field.ty;

        let stmt = if attrs.pagable {
            quote_spanned! { field.span()=>
                pagable::PagableSerialize::pagable_serialize(&self.#ident, ctx.pagable())?;
            }
        } else {
            quote_spanned! { field.span()=>
                <#ty as starlark::pagable::StarlarkSerialize>::starlark_serialize(&self.#ident, ctx)?;
            }
        };
        stmts.push(stmt);
    }

    Ok(quote! { #(#stmts)* })
}

pub fn derive_starlark_deserialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_starlark_deserialize_impl(&input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn derive_starlark_deserialize_impl(input: &DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let body = match &input.data {
        syn::Data::Struct(data) => gen_deserialize_struct(name, &data.fields)?,
        syn::Data::Enum(_) => {
            return Err(syn::Error::new_spanned(
                input,
                "StarlarkDeserialize derive does not support enums",
            ));
        }
        syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                input,
                "StarlarkDeserialize derive does not support unions",
            ));
        }
    };

    Ok(quote! {
        impl #impl_generics starlark::pagable::StarlarkDeserialize for #name #ty_generics #where_clause {
            fn starlark_deserialize(
                ctx: &mut dyn starlark::pagable::StarlarkDeserializeContext<'_>,
            ) -> starlark::Result<Self> {
                #body
            }
        }
    })
}

fn gen_deserialize_struct(name: &Ident, fields: &Fields) -> syn::Result<proc_macro2::TokenStream> {
    match fields {
        Fields::Named(named) => {
            let mut field_inits = Vec::new();
            for field in &named.named {
                let attrs = extract_field_attrs(&field.attrs)?;
                let ident = field.ident.as_ref().unwrap();
                let ty = &field.ty;

                let value = if attrs.pagable {
                    quote_spanned! { field.span()=>
                        <#ty as pagable::PagableDeserialize>::pagable_deserialize(ctx.pagable())?
                    }
                } else {
                    quote_spanned! { field.span()=>
                        <#ty as starlark::pagable::StarlarkDeserialize>::starlark_deserialize(ctx)?
                    }
                };
                field_inits.push(quote! { #ident: #value });
            }
            Ok(quote! {
                Ok(#name { #(#field_inits,)* })
            })
        }
        Fields::Unnamed(unnamed) => {
            let mut field_values = Vec::new();
            for field in &unnamed.unnamed {
                let attrs = extract_field_attrs(&field.attrs)?;
                let ty = &field.ty;

                let value = if attrs.pagable {
                    quote_spanned! { field.span()=>
                        <#ty as pagable::PagableDeserialize>::pagable_deserialize(ctx.pagable())?
                    }
                } else {
                    quote_spanned! { field.span()=>
                        <#ty as starlark::pagable::StarlarkDeserialize>::starlark_deserialize(ctx)?
                    }
                };
                field_values.push(value);
            }
            Ok(quote! {
                Ok(#name(#(#field_values,)*))
            })
        }
        Fields::Unit => Ok(quote! { Ok(#name) }),
    }
}
