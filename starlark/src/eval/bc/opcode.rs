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

use std::{any, any::TypeId, collections::HashMap, marker};

use gazebo::dupe::Dupe;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use once_cell::sync::Lazy;

use crate::eval::bc::{instr::BcInstr, instr_impl::*};

/// Bytecode instruction opcode.
#[derive(Debug, Copy, Clone, Dupe, Eq, PartialEq, FromPrimitive)]
#[repr(u32)]
pub(crate) enum BcOpcode {
    Dup,
    Pop,
    Const,
    Const2,
    Const3,
    Const4,
    LoadLocal,
    LoadLocal2,
    LoadLocal3,
    LoadLocal4,
    LoadLocalAndConst,
    LoadLocalCaptured,
    LoadModule,
    StoreLocal,
    StoreLocalCaptured,
    StoreModule,
    StoreModuleAndExport,
    Unpack,
    ArrayIndex,
    ArrayIndexNoPop,
    SetArrayIndex,
    ArrayIndexSet,
    Slice,
    ObjectField,
    SetObjectField,
    ObjectSetField,
    Eq,
    NotEq,
    Not,
    Minus,
    Plus,
    BitNot,
    Less,
    Greater,
    LessOrEqual,
    GreaterOrEqual,
    In,
    NotIn,
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
    Br,
    IfBr,
    IfNotBr,
    ForLoop,
    Break,
    Continue,
    Return,
    ReturnNone,
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
    Def,
    PossibleGc,
    BeforeStmt,
    ProfileBc,
    EndOfBc,
}

/// Callback for the `dispatch` function.
pub(crate) trait BcOpcodeHandler<R> {
    fn handle<I: BcInstr>(self) -> R;
}

impl BcOpcode {
    /// Opcode count.
    pub(crate) const COUNT: usize = (BcOpcode::EndOfBc as usize) + 1;

    /// Get opcode by opcode number.
    pub(crate) fn by_number(n: u32) -> Option<BcOpcode> {
        FromPrimitive::from_u32(n)
    }

    /// Invoke a callback parameterized by instruction type depending on
    /// this opcode.
    #[cfg_attr(not(debug_assertions), inline(always))]
    pub(crate) fn dispatch<R>(self, handler: impl BcOpcodeHandler<R>) -> R {
        match self {
            BcOpcode::Dup => handler.handle::<InstrDup>(),
            BcOpcode::Pop => handler.handle::<InstrPop>(),
            BcOpcode::Const => handler.handle::<InstrConst>(),
            BcOpcode::Const2 => handler.handle::<InstrConst2>(),
            BcOpcode::Const3 => handler.handle::<InstrConst3>(),
            BcOpcode::Const4 => handler.handle::<InstrConst4>(),
            BcOpcode::Type => handler.handle::<InstrType>(),
            BcOpcode::TypeIs => handler.handle::<InstrTypeIs>(),
            BcOpcode::Len => handler.handle::<InstrLen>(),
            BcOpcode::Not => handler.handle::<InstrNot>(),
            BcOpcode::Minus => handler.handle::<InstrMinus>(),
            BcOpcode::Plus => handler.handle::<InstrPlus>(),
            BcOpcode::BitNot => handler.handle::<InstrBitNot>(),
            BcOpcode::Eq => handler.handle::<InstrEq>(),
            BcOpcode::NotEq => handler.handle::<InstrNotEq>(),
            BcOpcode::In => handler.handle::<InstrIn>(),
            BcOpcode::NotIn => handler.handle::<InstrNotIn>(),
            BcOpcode::Add => handler.handle::<InstrAdd>(),
            BcOpcode::AddAssign => handler.handle::<InstrAddAssign>(),
            BcOpcode::Sub => handler.handle::<InstrSub>(),
            BcOpcode::Multiply => handler.handle::<InstrMultiply>(),
            BcOpcode::Percent => handler.handle::<InstrPercent>(),
            BcOpcode::PercentSOne => handler.handle::<InstrPercentSOne>(),
            BcOpcode::FormatOne => handler.handle::<InstrFormatOne>(),
            BcOpcode::Divide => handler.handle::<InstrDivide>(),
            BcOpcode::FloorDivide => handler.handle::<InstrFloorDivide>(),
            BcOpcode::BitAnd => handler.handle::<InstrBitAnd>(),
            BcOpcode::BitOr => handler.handle::<InstrBitOr>(),
            BcOpcode::BitXor => handler.handle::<InstrBitXor>(),
            BcOpcode::LeftShift => handler.handle::<InstrLeftShift>(),
            BcOpcode::RightShift => handler.handle::<InstrRightShift>(),
            BcOpcode::Less => handler.handle::<InstrLess>(),
            BcOpcode::Greater => handler.handle::<InstrGreater>(),
            BcOpcode::LessOrEqual => handler.handle::<InstrLessOrEqual>(),
            BcOpcode::GreaterOrEqual => handler.handle::<InstrGreaterOrEqual>(),
            BcOpcode::Br => handler.handle::<InstrBr>(),
            BcOpcode::IfBr => handler.handle::<InstrIfBr>(),
            BcOpcode::IfNotBr => handler.handle::<InstrIfNotBr>(),
            BcOpcode::ForLoop => handler.handle::<InstrForLoop>(),
            BcOpcode::Break => handler.handle::<InstrBreak>(),
            BcOpcode::Continue => handler.handle::<InstrContinue>(),
            BcOpcode::LoadLocal => handler.handle::<InstrLoadLocal>(),
            BcOpcode::LoadLocal2 => handler.handle::<InstrLoadLocal2>(),
            BcOpcode::LoadLocal3 => handler.handle::<InstrLoadLocal3>(),
            BcOpcode::LoadLocal4 => handler.handle::<InstrLoadLocal4>(),
            BcOpcode::LoadLocalAndConst => handler.handle::<InstrLoadLocalAndConst>(),
            BcOpcode::LoadLocalCaptured => handler.handle::<InstrLoadLocalCaptured>(),
            BcOpcode::LoadModule => handler.handle::<InstrLoadModule>(),
            BcOpcode::StoreLocal => handler.handle::<InstrStoreLocal>(),
            BcOpcode::StoreLocalCaptured => handler.handle::<InstrStoreLocalCaptured>(),
            BcOpcode::StoreModule => handler.handle::<InstrStoreModule>(),
            BcOpcode::StoreModuleAndExport => handler.handle::<InstrStoreModuleAndExport>(),
            BcOpcode::Unpack => handler.handle::<InstrUnpack>(),
            BcOpcode::ArrayIndex => handler.handle::<InstrArrayIndex>(),
            BcOpcode::ArrayIndexNoPop => handler.handle::<InstrArrayIndexNoPop>(),
            BcOpcode::SetArrayIndex => handler.handle::<InstrSetArrayIndex>(),
            BcOpcode::ArrayIndexSet => handler.handle::<InstrArrayIndexSet>(),
            BcOpcode::ObjectField => handler.handle::<InstrObjectField>(),
            BcOpcode::SetObjectField => handler.handle::<InstrSetObjectField>(),
            BcOpcode::ObjectSetField => handler.handle::<InstrObjectSetField>(),
            BcOpcode::Slice => handler.handle::<InstrSlice>(),
            BcOpcode::ListNPop => handler.handle::<InstrListNPop>(),
            BcOpcode::ListOfConsts => handler.handle::<InstrListOfConsts>(),
            BcOpcode::DictOfConsts => handler.handle::<InstrDictOfConsts>(),
            BcOpcode::TupleNPop => handler.handle::<InstrTupleNPop>(),
            BcOpcode::DictNPop => handler.handle::<InstrDictNPop>(),
            BcOpcode::ListNew => handler.handle::<InstrListNew>(),
            BcOpcode::DictNew => handler.handle::<InstrDictNew>(),
            BcOpcode::DictConstKeys => handler.handle::<InstrDictConstKeys>(),
            BcOpcode::ComprListAppend => handler.handle::<InstrComprListAppend>(),
            BcOpcode::ComprDictInsert => handler.handle::<InstrComprDictInsert>(),
            BcOpcode::Def => handler.handle::<InstrDef>(),
            BcOpcode::Call => handler.handle::<InstrCall>(),
            BcOpcode::CallPos => handler.handle::<InstrCallPos>(),
            BcOpcode::CallFrozenDef => handler.handle::<InstrCallFrozenDef>(),
            BcOpcode::CallFrozenDefPos => handler.handle::<InstrCallFrozenDefPos>(),
            BcOpcode::CallFrozenNative => handler.handle::<InstrCallFrozenNative>(),
            BcOpcode::CallFrozenNativePos => handler.handle::<InstrCallFrozenNativePos>(),
            BcOpcode::CallFrozen => handler.handle::<InstrCallFrozen>(),
            BcOpcode::CallFrozenPos => handler.handle::<InstrCallFrozenPos>(),
            BcOpcode::CallMethod => handler.handle::<InstrCallMethod>(),
            BcOpcode::CallMethodPos => handler.handle::<InstrCallMethodPos>(),
            BcOpcode::Return => handler.handle::<InstrReturn>(),
            BcOpcode::ReturnNone => handler.handle::<InstrReturnNone>(),
            BcOpcode::PossibleGc => handler.handle::<InstrPossibleGc>(),
            BcOpcode::BeforeStmt => handler.handle::<InstrBeforeStmt>(),
            BcOpcode::ProfileBc => handler.handle::<InstrProfileBc>(),
            BcOpcode::EndOfBc => handler.handle::<InstrEndOfBc>(),
        }
    }

    /// Iterate over the bytecode opcodes.
    pub(crate) fn iter() -> impl Iterator<Item = BcOpcode> {
        (0..BcOpcode::COUNT).map(|i| BcOpcode::by_number(i as u32).unwrap())
    }

    /// Does given instruction have this opcode?
    fn is_for_instr<I: BcInstr>(self) -> bool {
        struct Is<J: BcInstr> {
            _marker: marker::PhantomData<J>,
        }

        impl<J: BcInstr> BcOpcodeHandler<bool> for Is<J> {
            fn handle<I: BcInstr>(self) -> bool {
                TypeId::of::<I>() == TypeId::of::<J>()
            }
        }

        self.dispatch(Is::<I> {
            _marker: marker::PhantomData,
        })
    }

    /// Find bytecode opcode by instruction, panic if not found.
    fn find_for_instr<I: BcInstr>() -> BcOpcode {
        BcOpcode::iter()
            .find(|opcode| opcode.is_for_instr::<I>())
            .unwrap_or_else(|| {
                panic!(
                    "No bytecode opcode for instruction {:?}",
                    any::type_name::<I>()
                )
            })
    }

    /// Get bytecode opcode for the instruction.
    pub(crate) fn for_instr<I: BcInstr>() -> BcOpcode {
        // `find_for_instr` is optimized away in release mode,
        // but it is quadratic in debug mode.
        // https://rust.godbolt.org/z/8fWcPxc3Y
        // So we use it directly  in release, but create an index in debug.
        // Note both branches are typechecked in both modes.
        if !cfg!(debug_assertions) {
            BcOpcode::find_for_instr::<I>()
        } else {
            struct Index {
                instr_type_id_to_opcode: HashMap<TypeId, BcOpcode>,
            }
            static INDEX: Lazy<Index> = Lazy::new(|| {
                let mut map = HashMap::new();
                for opcode in BcOpcode::iter() {
                    struct AddToMap<'m> {
                        map: &'m mut HashMap<TypeId, BcOpcode>,
                        opcode: BcOpcode,
                    }
                    impl BcOpcodeHandler<()> for AddToMap<'_> {
                        fn handle<J: BcInstr>(self) {
                            let prev = self.map.insert(TypeId::of::<J>(), self.opcode);
                            assert!(
                                prev.is_none(),
                                "Non-unique entry for {}",
                                any::type_name::<J>()
                            );
                        }
                    }
                    opcode.dispatch(AddToMap {
                        map: &mut map,
                        opcode,
                    });
                }
                Index {
                    instr_type_id_to_opcode: map,
                }
            });
            *INDEX
                .instr_type_id_to_opcode
                .get(&TypeId::of::<I>())
                .unwrap_or_else(|| {
                    panic!(
                        "No bytecode opcode for instruction {:?}",
                        any::type_name::<I>()
                    )
                })
        }
    }
}

#[cfg(test)]
mod test {
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
