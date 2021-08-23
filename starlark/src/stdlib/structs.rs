/*
 * Copyright 2018 The Starlark in Rust Authors.
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

//! Implementation of `struct` function.
use crate as starlark;
use crate::{
    environment::GlobalsBuilder,
    eval::Arguments,
    values::{structs::Struct, Value, ValueLike},
};

#[starlark_module]
pub fn global(builder: &mut GlobalsBuilder) {
    #[starlark_type(Struct::TYPE)]
    fn r#struct(args: Arguments<'v, '_>) -> Struct<'v> {
        args.no_positional_args(heap)?;
        Ok(Struct {
            fields: args.names()?.content,
        })
    }
}

#[starlark_module]
pub(crate) fn struct_methods(builder: &mut GlobalsBuilder) {
    fn to_json(this: Value) -> String {
        this.to_json()
    }
}
