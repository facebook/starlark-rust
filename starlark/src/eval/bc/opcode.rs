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

//! Instruction opcode.

use std::any;
use std::any::TypeId;
use std::marker;

use dupe::Dupe;
use starlark_derive::starlark_internal_bc;

use crate::eval::bc::instr::BcInstr;
use crate::eval::bc::instr_impl::*;

/// Bytecode instruction opcode.
#[starlark_internal_bc]
#[derive(Debug, Copy, Clone, Dupe, Eq, PartialEq, PartialOrd, Ord, Hash)]
#[repr(u32)]
pub(crate) enum BcOpcode {
    Const,
    LoadLocal,
    LoadLocalCaptured,
    LoadModule,
    Mov,
    StoreLocalCaptured,
    StoreModule,
    StoreModuleAndExport,
    Unpack,
    ArrayIndex,
    SetArrayIndex,
    ArrayIndexSet,
    Slice,
    ObjectField,
    ObjectFieldRaw,
    SetObjectField,
    Eq,
    EqConst,
    EqPtr,
    EqStr,
    EqInt,
    Not,
    Minus,
    Plus,
    BitNot,
    Less,
    Greater,
    LessOrEqual,
    GreaterOrEqual,
    In,
    Add,
    AddAssign,
    Sub,
    Multiply,
    Percent,
    PercentSOne,
    FormatOne,
    Divide,
    FloorDivide,
    BitAnd,
    BitOr,
    BitOrAssign,
    BitXor,
    LeftShift,
    RightShift,
    Len,
    Type,
    TypeIs,
    TupleNPop,
    ListNew,
    ListNPop,
    ListOfConsts,
    DictNew,
    DictNPop,
    DictOfConsts,
    DictConstKeys,
    ComprListAppend,
    ComprDictInsert,
    CheckType,
    Br,
    IfBr,
    IfNotBr,
    Iter,
    Continue,
    Break,
    IterStop,
    Return,
    ReturnConst,
    ReturnCheckType,
    Call,
    CallPos,
    CallFrozenDef,
    CallFrozenDefPos,
    CallFrozenNative,
    CallFrozenNativePos,
    CallFrozen,
    CallFrozenPos,
    CallMethod,
    CallMethodPos,
    CallMaybeKnownMethod,
    CallMaybeKnownMethodPos,
    Def,
    PossibleGc,
    End,
}

/// Callback for the `dispatch` function.
pub(crate) trait BcOpcodeHandler<R> {
    fn handle<I: BcInstr>(self) -> R;
}

/// Callback for the `dispatch_all` function.
pub(crate) trait BcOpcodeAllHandler {
    fn handle<I: BcInstr>(&mut self, opcode: BcOpcode);
}

impl BcOpcode {
    /// Opcode count.
    pub(crate) const COUNT: usize = (BcOpcode::End as usize) + 1;

    /// Invoke a callback parameterized by instruction type depending on
    /// this opcode.
    #[cfg_attr(not(debug_assertions), inline(always))]
    pub(crate) fn dispatch<R>(self, handler: impl BcOpcodeHandler<R>) -> R {
        // Call a function generated by proc macro.
        self.do_dispatch(handler)
    }

    /// Invoke a callback parameterized by instruction type for each opcode.
    #[inline(always)]
    pub(crate) fn dispatch_all(handler: &mut impl BcOpcodeAllHandler) {
        // Call a function generated by proc macro.
        BcOpcode::do_dispatch_all(handler)
    }

    /// Get opcode by opcode number.
    pub(crate) fn by_number(n: u32) -> Option<BcOpcode> {
        struct ByNumber {
            i: u32,
            n: u32,
            opcode: Option<BcOpcode>,
        }
        impl BcOpcodeAllHandler for ByNumber {
            fn handle<I: BcInstr>(&mut self, opcode: BcOpcode) {
                if self.i == self.n {
                    self.opcode = Some(opcode);
                }
                self.i += 1;
            }
        }
        let mut by_number = ByNumber {
            i: 0,
            n,
            opcode: None,
        };
        BcOpcode::do_dispatch_all(&mut by_number);
        by_number.opcode
    }

    /// Get bytecode opcode for the instruction.
    pub(crate) fn for_instr<I: BcInstr>() -> BcOpcode {
        struct FindOpcode<I: BcInstr> {
            opcode: Option<BcOpcode>,
            _marker: marker::PhantomData<I>,
        }

        impl<I: BcInstr> BcOpcodeAllHandler for FindOpcode<I> {
            fn handle<J: BcInstr>(&mut self, opcode: BcOpcode) {
                if TypeId::of::<I>() == TypeId::of::<J>() {
                    assert!(self.opcode.is_none());
                    self.opcode = Some(opcode);
                }
            }
        }

        let mut find_opcode = FindOpcode::<I> {
            opcode: None,
            _marker: marker::PhantomData,
        };
        Self::dispatch_all(&mut find_opcode);
        find_opcode
            .opcode
            .unwrap_or_else(|| panic!("No opcode for instruction {:?}", any::type_name::<I>()))
    }
}

#[cfg(test)]
mod tests {
    use crate::eval::bc::opcode::BcOpcode;

    #[test]
    fn opcode_count() {
        for i in 0..10000 {
            if i < (BcOpcode::COUNT as u32) {
                assert!(BcOpcode::by_number(i).is_some());
            } else {
                assert!(BcOpcode::by_number(i).is_none());
            }
        }
    }
}
