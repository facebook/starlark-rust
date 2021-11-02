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

//! Compile function calls.

use std::convert::TryInto;

use either::Either;

use crate::{
    codemap::{Span, Spanned},
    collections::symbol_map::Symbol,
    eval::{
        bc::{
            compiler::expr::write_exprs,
            instr_arg::{ArgPopsStack, ArgPopsStack1},
            instr_impl::{
                InstrCall, InstrCallFrozen, InstrCallFrozenDef, InstrCallFrozenDefPos,
                InstrCallFrozenNative, InstrCallFrozenNativePos, InstrCallFrozenPos,
                InstrCallMethod, InstrCallMethodPos, InstrCallPos,
            },
            writer::BcWriter,
        },
        fragment::call::{ArgsCompiledValue, CallCompiled},
        FrozenDef,
    },
    values::{function::NativeFunction, typed::FrozenValueTyped, FrozenStringValue, FrozenValue},
};

#[derive(Debug)]
pub(crate) struct ArgsCompiledValueBc {
    pub(crate) span: Span,
    pub(crate) pos_named: u32,
    pub(crate) names: Box<[(Symbol, FrozenStringValue)]>,
    pub(crate) args: bool,
    pub(crate) kwargs: bool,
}

impl ArgsCompiledValue {
    fn write_bc(&self, span: Span, bc: &mut BcWriter) -> ArgsCompiledValueBc {
        write_exprs(&self.pos_named, bc);
        write_exprs(&self.args, bc);
        write_exprs(&self.kwargs, bc);
        ArgsCompiledValueBc {
            span,
            pos_named: self.pos_named.len().try_into().unwrap(),
            names: self.names.clone().into_boxed_slice(),
            args: self.args.is_some(),
            kwargs: self.kwargs.is_some(),
        }
    }
}

impl Spanned<CallCompiled> {
    fn write_args(
        span: Span,
        args: &ArgsCompiledValue,
        bc: &mut BcWriter,
    ) -> Either<ArgPopsStack, ArgsCompiledValueBc> {
        if let Some(pos) = args.pos_only() {
            write_exprs(pos, bc);
            Either::Left(ArgPopsStack(pos.len() as u32))
        } else {
            let args = args.write_bc(span, bc);
            Either::Right(args)
        }
    }

    fn write_call_frozen(
        span: Span,
        fun: FrozenValue,
        args: &ArgsCompiledValue,
        bc: &mut BcWriter,
    ) {
        if let Some(fun) = FrozenValueTyped::<FrozenDef>::new(fun) {
            match Self::write_args(span, args, bc) {
                Either::Left(npops) => {
                    bc.write_instr::<InstrCallFrozenDefPos>(span, (npops, fun, span));
                }
                Either::Right(args) => {
                    bc.write_instr::<InstrCallFrozenDef>(span, (fun, args));
                }
            }
        } else if let Some(fun) = FrozenValueTyped::<NativeFunction>::new(fun) {
            match Self::write_args(span, args, bc) {
                Either::Left(npops) => {
                    bc.write_instr::<InstrCallFrozenNativePos>(span, (npops, fun, span));
                }
                Either::Right(args) => {
                    bc.write_instr::<InstrCallFrozenNative>(span, (fun, args));
                }
            }
        } else {
            match Self::write_args(span, args, bc) {
                Either::Left(npops) => {
                    bc.write_instr::<InstrCallFrozenPos>(span, (npops, fun, span));
                }
                Either::Right(args) => {
                    bc.write_instr::<InstrCallFrozen>(span, (fun, args));
                }
            }
        }
    }

    pub(crate) fn write_bc(&self, bc: &mut BcWriter) {
        let span = self.span;
        match self.node {
            CallCompiled::Call(box (ref f, ref args)) => match f.as_value() {
                Some(f) => Self::write_call_frozen(span, f, args, bc),
                None => {
                    f.write_bc(bc);
                    match Self::write_args(span, args, bc) {
                        Either::Left(npops) => {
                            bc.write_instr::<InstrCallPos>(span, (ArgPopsStack1, npops, span))
                        }
                        Either::Right(args) => {
                            bc.write_instr::<InstrCall>(span, (ArgPopsStack1, args));
                        }
                    }
                }
            },
            CallCompiled::Method(box (ref this, ref symbol, ref args)) => {
                this.write_bc(bc);
                if let Some(pos) = args.pos_only() {
                    write_exprs(pos, bc);
                    let symbol = symbol.clone();
                    bc.write_instr::<InstrCallMethodPos>(
                        span,
                        (ArgPopsStack1, ArgPopsStack(pos.len() as u32), symbol, span),
                    );
                } else {
                    let args = args.write_bc(span, bc);
                    bc.write_instr::<InstrCallMethod>(span, (ArgPopsStack1, symbol.clone(), args));
                }
            }
        }
    }
}
