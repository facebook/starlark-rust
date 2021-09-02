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
use syn::*;

pub(crate) fn parse(mut input: ItemFn) -> StarModule {
    let visibility = input.vis;
    let name = input.sig.ident;
    let ty = match input.sig.inputs.pop().map(|x| x.into_value()) {
        Some(FnArg::Typed(PatType { ty, .. })) if is_mut_globals_builder(&ty) => ty,
        _ => panic!("Must take on argument of type &mut GlobalsBuilder"),
    };
    StarModule {
        visibility,
        globals_builder: *ty,
        name,
        stmts: input.block.stmts.into_map(parse_stmt),
    }
}

fn parse_stmt(stmt: Stmt) -> StarStmt {
    match stmt {
        Stmt::Item(Item::Fn(x)) => parse_fun(x),
        Stmt::Item(Item::Const(x)) => StarStmt::Const(parse_const(x)),
        _ => panic!("Can only put constants and functions inside a #[starlark_module]"),
    }
}

fn parse_const(x: ItemConst) -> StarConst {
    StarConst {
        name: x.ident,
        ty: *x.ty,
        value: *x.expr,
    }
}

fn is_attribute_attribute(x: &Attribute) -> bool {
    x.path.is_ident("attribute")
}

fn is_attribute_type(x: &Attribute) -> Option<NestedMeta> {
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

struct ProcessedAttributes {
    is_attribute: bool,
    type_attribute: Option<NestedMeta>,
    /// Rest attributes
    attrs: Vec<Attribute>,
}

/// (#[attribute], #[starlark_type(x)], rest)
fn process_attributes(xs: Vec<Attribute>) -> ProcessedAttributes {
    let mut attrs = Vec::with_capacity(xs.len());
    let mut is_attribute = false;
    let mut type_attribute = None;
    for x in xs {
        if is_attribute_attribute(&x) {
            is_attribute = true;
        } else if let Some(t) = is_attribute_type(&x) {
            type_attribute = Some(t);
        } else {
            attrs.push(x);
        }
    }
    if is_attribute {
        assert!(
            type_attribute.is_none(),
            "Can't be an attribute with a .type"
        );
    }
    ProcessedAttributes {
        is_attribute,
        type_attribute,
        attrs,
    }
}

// Add a function to the `GlobalsModule` named `globals_builder`.
fn parse_fun(func: ItemFn) -> StarStmt {
    let ProcessedAttributes {
        is_attribute,
        type_attribute,
        attrs,
    } = process_attributes(func.attrs);

    let return_type = match func.sig.output {
        ReturnType::Default => panic!(
            "Function named '{}' must have a return type",
            func.sig.ident
        ),
        ReturnType::Type(_, x) => x,
    };
    let mut args = func
        .sig
        .inputs
        .into_iter()
        .map(parse_arg)
        .collect::<Vec<_>>();

    if is_attribute {
        assert_eq!(args.len(), 1);
        let arg = args.pop().unwrap();
        assert!(arg.is_this() && arg.default.is_none());
        StarStmt::Attr(StarAttr {
            name: func.sig.ident,
            arg: arg.ty,
            attrs,
            return_type: *return_type,
            body: *func.block,
        })
    } else {
        StarStmt::Fun(StarFun {
            name: func.sig.ident,
            type_attribute,
            attrs,
            args,
            return_type: *return_type,
            body: *func.block,
            source: StarFunSource::Unknown,
        })
    }
}

fn parse_arg(x: FnArg) -> StarArg {
    match x {
        FnArg::Typed(PatType {
            attrs,
            pat: box Pat::Ident(ident),
            ty: box ty,
            ..
        }) => StarArg {
            attrs,
            mutable: ident.mutability.is_some(),
            name: ident.ident,
            by_ref: ident.by_ref.is_some(),
            ty,
            default: ident.subpat.map(|x| *x.1),
            source: StarArgSource::Unknown,
        },
        arg => panic!("Unexpected argument, {:?}", arg),
    }
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
