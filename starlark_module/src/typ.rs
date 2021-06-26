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

use crate::util::*;
use syn::*;

#[derive(Debug)]
pub(crate) struct StarModule {
    pub visibility: Visibility,
    // We reuse the users globals_builder to make sure `use` statements etc
    // make sense
    pub globals_builder: Type,
    pub name: Ident,
    pub stmts: Vec<StarStmt>,
}

#[derive(Debug)]
pub(crate) enum StarStmt {
    Const(StarConst),
    Fun(StarFun),
    Attr(StarAttr),
}

#[derive(Debug)]
pub(crate) struct StarConst {
    pub name: Ident,
    pub ty: Type,
    pub value: Expr,
}

#[derive(Debug)]
pub(crate) struct StarFun {
    pub name: Ident,
    pub type_attribute: Option<NestedMeta>,
    pub attrs: Vec<Attribute>,
    pub args: Vec<StarArg>,
    pub return_type: Type,
    pub body: Block,
}

#[derive(Debug)]
pub(crate) struct StarAttr {
    pub name: Ident,
    pub arg: Type,
    pub attrs: Vec<Attribute>,
    pub return_type: Type,
    pub body: Block,
}

#[derive(Debug)]
pub(crate) struct StarArg {
    pub attrs: Vec<Attribute>,
    pub mutable: bool,
    pub by_ref: bool,
    pub name: Ident,
    pub ty: Type,
    pub default: Option<Pat>,
}

impl StarArg {
    pub fn is_option(&self) -> bool {
        is_type_name(&self.ty, "Option")
    }

    pub fn is_value(&self) -> bool {
        is_type_name(&self.ty, "Value")
    }

    pub fn is_this(&self) -> bool {
        self.name == "this" || self.name == "_this"
    }

    pub fn is_args(&self) -> bool {
        self.name == "args"
    }

    pub fn is_kwargs(&self) -> bool {
        self.name == "kwargs"
    }
}
