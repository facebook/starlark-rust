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
    pub source: StarFunSource,
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
    pub source: StarArgSource,
}

#[derive(Debug)]
pub(crate) enum StarArgSource {
    Unknown,
    This,
    Parameters,
    Argument(usize),
    Required(usize),
    Optional(usize),
}

#[derive(Debug)]
pub(crate) enum StarFunSource {
    Unknown,
    Parameters,
    Argument(usize),
    Positional(usize, usize),
}

impl StarModule {
    pub fn resolve(&mut self) {
        for x in &mut self.stmts {
            if let StarStmt::Fun(x) = x {
                x.resolve()
            }
        }
    }
}

impl StarFun {
    #[allow(clippy::branches_sharing_code)] // False positive
    pub fn resolve(&mut self) {
        fn requires_signature(x: &StarArg) -> bool {
            // We need to use a signature if something has a name
            // There are *args or **kwargs
            // There is a default that needs promoting to a Value (since the signature stores that value)
            !x.by_ref || x.is_args() || x.is_kwargs() || (x.is_value() && x.default.is_some())
        }

        if self.args.len() == 1 && self.args[0].is_arguments() {
            self.args[0].source = StarArgSource::Parameters;
            self.source = StarFunSource::Parameters;
        } else {
            let use_arguments = self
                .args
                .iter()
                .filter(|x| !x.is_this())
                .any(requires_signature);
            if use_arguments {
                let mut argument = 0;
                for x in &mut self.args {
                    if x.is_this() {
                        x.source = StarArgSource::This;
                    } else {
                        x.source = StarArgSource::Argument(argument);
                        argument += 1;
                    }
                }
                self.source = StarFunSource::Argument(argument);
            } else {
                let mut required = 0;
                let mut optional = 0;
                for x in &mut self.args {
                    if x.is_this() {
                        x.source = StarArgSource::This;
                        continue;
                    }
                    if optional == 0 && x.default.is_none() && !x.is_option() {
                        x.source = StarArgSource::Required(required);
                        required += 1;
                    } else {
                        x.source = StarArgSource::Optional(optional);
                        optional += 1;
                    }
                }
                self.source = StarFunSource::Positional(required, optional);
            }
        }
    }
}

impl StarArg {
    pub fn is_arguments(&self) -> bool {
        is_type_name(&self.ty, "Arguments")
    }

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
