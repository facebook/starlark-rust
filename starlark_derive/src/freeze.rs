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

use proc_macro2::{Ident, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    parse::ParseStream, parse_macro_input, spanned::Spanned, Attribute, Data, DataEnum, DataStruct,
    DeriveInput, Fields, GenericParam, LifetimeDef, TypeParam,
};

struct Input<'a> {
    input: &'a DeriveInput,
}

impl<'a> Input<'a> {
    fn lifetime_param(&self) -> Option<&LifetimeDef> {
        let mut lifetime_defs: Vec<_> = self
            .input
            .generics
            .params
            .iter()
            .filter_map(|param| match param {
                GenericParam::Lifetime(d) => {
                    assert!(d.lifetime.ident == "v", "Lifetime param must be called 'v");
                    Some(d)
                }
                _ => None,
            })
            .collect();
        assert!(lifetime_defs.len() <= 1, "More than one lifetime param");
        lifetime_defs.pop()
    }

    fn type_params(&self) -> Vec<&TypeParam> {
        self.input
            .generics
            .params
            .iter()
            .filter_map(|param| match param {
                GenericParam::Type(t) => Some(t),
                _ => None,
            })
            .collect()
    }

    fn make_input_params(&self) -> Vec<TokenStream> {
        let mut params = Vec::new();
        if let Some(p) = self.lifetime_param() {
            let lt = GenericParam::Lifetime(p.clone());
            params.push(quote! { #lt });
        }
        for _ in 0..self.type_params().len() {
            params.push(quote! { starlark::values::Value<'v> });
        }
        params
    }

    fn format_input_params(&self) -> TokenStream {
        let params = self.make_input_params();
        if params.is_empty() {
            quote! {}
        } else {
            quote! { < #(#params,)* > }
        }
    }

    fn make_output_params(&self) -> Vec<TokenStream> {
        let mut params = Vec::new();
        if self.lifetime_param().is_some() {
            params.push(quote! { 'static })
        }
        for _ in 0..self.type_params().len() {
            params.push(quote! { starlark::values::FrozenValue });
        }
        params
    }

    fn format_output_params(&self) -> TokenStream {
        let params = self.make_output_params();
        if params.is_empty() {
            quote! {}
        } else {
            quote! { < #(#params,)* > }
        }
    }

    fn format_impl_generics(&self) -> TokenStream {
        if let Some(generics) = self.lifetime_param() {
            quote! { < #generics > }
        } else if !self.type_params().is_empty() {
            quote! { < 'v > }
        } else {
            quote! {}
        }
    }
}

pub fn derive_freeze(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let input = Input { input: &input };

    let name = &input.input.ident;

    let input_params = input.format_input_params();
    let output_params = input.format_output_params();
    let impl_generics = input.format_impl_generics();

    let body = freeze_impl(name, &input.input.data);
    let gen = quote! {
        impl #impl_generics starlark::values::Freeze for #name #input_params {
            type Frozen = #name #output_params;
            fn freeze(self, freezer: &starlark::values::Freezer) -> anyhow::Result<Self::Frozen> {
                #body
            }
        }
    };
    gen.into()
}

/// Parse attribute `#[freeze(identity)]`.
///
/// Currently it fails on any attribute argument other than `id`.
fn is_identity(attrs: &[Attribute]) -> bool {
    syn::custom_keyword!(identity);

    attrs.iter().any(|a| {
        a.path.is_ident("freeze")
            && a.parse_args_with(|input: ParseStream| {
                let ignore = input.parse::<Option<identity>>()?.is_some();
                Ok(ignore)
            })
            .unwrap()
    })
}

fn freeze_struct(name: &Ident, data: &DataStruct) -> TokenStream {
    match data.fields {
        Fields::Named(ref fields) => {
            let xs: Vec<_> = fields
                .named
                .iter()
                .map(|f| {
                    let name = &f.ident;
                    if is_identity(&f.attrs) {
                        quote_spanned! {f.span() =>
                            #name: self.#name,
                        }
                    } else {
                        quote_spanned! {f.span() =>
                            #name: starlark::values::Freeze::freeze(self.#name, freezer)?,
                        }
                    }
                })
                .collect();
            quote! {
                std::result::Result::Ok(#name {
                    #(#xs)*
                })
            }
        }
        Fields::Unnamed(ref fields) => {
            let xs: Vec<_> = fields
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, f)| {
                    if is_identity(&f.attrs) {
                        quote_spanned! {f.span() =>
                            self.#i
                        }
                    } else {
                        quote_spanned! {f.span() => starlark::values::FreezeField::freeze_field(self.#i, freezer)?}
                    }
                })
                .collect();
            quote! {
                std::result::Result::Ok(#name (
                    #(#xs)*
                ))
            }
        }
        Fields::Unit => {
            quote!()
        }
    }
}

fn freeze_enum(_name: &Ident, _data: &DataEnum) -> TokenStream {
    unimplemented!("Can't derive freeze for enums");
}

fn freeze_impl(name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data) => freeze_struct(name, data),
        Data::Enum(data) => freeze_enum(name, data),
        Data::Union(_) => unimplemented!("Can't derive freeze for unions"),
    }
}
