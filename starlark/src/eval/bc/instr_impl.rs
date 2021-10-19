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

//! Instruction implementations.

use std::{cmp::Ordering, marker, mem::MaybeUninit};

use gazebo::coerce::coerce;

use crate::{
    codemap::{Span, Spanned},
    collections::{symbol_map::Symbol, Hashed, SmallMap},
    environment::slots::ModuleSlotId,
    eval::{
        bc::{
            addr::{BcAddr, BcAddrOffset, BcPtrAddr},
            bytecode::{run_block, Bc, RunBlockResult},
            compiler::call::ArgsCompiledValueBc,
            instr::{BcInstr, InstrControl},
            instr_arg::{
                ArgPopsStack, ArgPopsStack1, ArgPopsStackMaybe1, ArgPushesStack, BcInstrArg,
            },
            opcode::BcOpcode,
            stack_ptr::BcStackPtr,
            stack_values::BcStackValues,
        },
        compiler::{add_span_to_expr_error, expr_throw, scope::Captured, EvalException},
        fragment::{
            def::{DefInfo, ParameterCompiled},
            expr::{get_attr_hashed, EvalError},
            stmt::{add_assign, before_stmt, possible_gc, AssignError},
        },
        runtime::slots::LocalSlotId,
        Def, Evaluator, FrozenDef, ParametersSpec,
    },
    values::{
        dict::Dict,
        function::{BoundMethod, NativeAttribute, NativeFunction},
        interpolation::{format_one, percent_s_one},
        list::List,
        typed::FrozenValueTyped,
        typing::TypeCompiled,
        AttrType, FrozenRef, FrozenStringValue, FrozenValue, Heap, StarlarkValue, Value, ValueLike,
    },
};

/// Instructions which either fail or proceed to the following instruction,
/// and it returns error with span.
pub(crate) trait InstrNoFlowImpl: 'static {
    const OPCODE: BcOpcode;
    type Pop<'v>: BcStackValues<'v>;
    type Push<'v>: BcStackValues<'v>;
    type Arg: BcInstrArg;

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr,
        arg: &Self::Arg,
        pops: Self::Pop<'v>,
    ) -> Result<Self::Push<'v>, EvalException>;
}

pub(crate) struct InstrNoFlow<I: InstrNoFlowImpl>(marker::PhantomData<I>);

impl<I: InstrNoFlowImpl> BcInstr for InstrNoFlow<I> {
    const OPCODE: BcOpcode = I::OPCODE;
    type Pop<'v> = I::Pop<'v>;
    type Push<'v> = I::Push<'v>;
    type Arg = I::Arg;

    #[inline(always)]
    fn run<'v, 'b>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr<'b>,
        arg: &Self::Arg,
    ) -> InstrControl<'v, 'b> {
        let pops = BcStackValues::pop(stack);
        match I::run_with_args(eval, stack, ip, arg, pops) {
            Ok(pushes) => {
                BcStackValues::push(stack, pushes);
                InstrControl::Next(ip.add_instr::<Self>())
            }
            Err(e) => InstrControl::Err(e),
        }
    }
}

pub(crate) struct InstrNoFlowAddSpanWrapper<I: InstrNoFlowAddSpanImpl>(marker::PhantomData<I>);
pub(crate) type InstrNoFlowAddSpan<I> = InstrNoFlow<InstrNoFlowAddSpanWrapper<I>>;

/// Instructions which either fail or proceed to the following instruction.
pub(crate) trait InstrNoFlowAddSpanImpl: 'static {
    const OPCODE: BcOpcode;
    type Pop<'v>: BcStackValues<'v>;
    type Push<'v>: BcStackValues<'v>;
    type Arg: BcInstrArg;

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        arg: &Self::Arg,
        pops: Self::Pop<'v>,
    ) -> Result<Self::Push<'v>, anyhow::Error>;
}

impl<I: InstrNoFlowAddSpanImpl> InstrNoFlowImpl for InstrNoFlowAddSpanWrapper<I> {
    const OPCODE: BcOpcode = I::OPCODE;
    type Pop<'v> = I::Pop<'v>;
    type Push<'v> = I::Push<'v>;
    type Arg = I::Arg;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr,
        arg: &Self::Arg,
        pops: Self::Pop<'v>,
    ) -> Result<Self::Push<'v>, EvalException> {
        match I::run_with_args(eval, stack, arg, pops) {
            Ok(pushs) => Ok(pushs),
            Err(e) => Err(Bc::wrap_error_for_instr_ptr(ip, e, eval)),
        }
    }
}

pub(crate) struct InstrDupImpl;
pub(crate) struct InstrPopImpl;

pub(crate) type InstrDup = InstrNoFlow<InstrDupImpl>;
pub(crate) type InstrPop = InstrNoFlow<InstrPopImpl>;

impl InstrNoFlowImpl for InstrDupImpl {
    const OPCODE: BcOpcode = BcOpcode::Dup;
    type Pop<'v> = Value<'v>;
    type Push<'v> = [Value<'v>; 2];
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        (): &(),
        v: Value<'v>,
    ) -> Result<[Value<'v>; 2], EvalException> {
        Ok([v, v])
    }
}

impl InstrNoFlowImpl for InstrPopImpl {
    const OPCODE: BcOpcode = BcOpcode::Pop;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        (): &(),
        _v: Value<'v>,
    ) -> Result<(), EvalException> {
        Ok(())
    }
}

pub(crate) struct InstrConstImpl;
pub(crate) type InstrConst = InstrNoFlow<InstrConstImpl>;

impl InstrNoFlowImpl for InstrConstImpl {
    const OPCODE: BcOpcode = BcOpcode::Const;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = FrozenValue;

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        arg: &FrozenValue,
        (): (),
    ) -> Result<Value<'v>, EvalException> {
        Ok(arg.to_value())
    }
}

macro_rules! instr_const_n {
    ($n:expr, $struct_name:ident, $impl_name:ident, $opcode:ident) => {
        pub(crate) struct $impl_name;
        pub(crate) type $struct_name = InstrNoFlow<$impl_name>;

        impl InstrNoFlowImpl for $impl_name {
            const OPCODE: BcOpcode = BcOpcode::$opcode;
            type Pop<'v> = ();
            type Push<'v> = [Value<'v>; $n];
            type Arg = [FrozenValue; $n];

            #[inline(always)]
            fn run_with_args<'v>(
                _eval: &mut Evaluator<'v, '_>,
                _stack: &mut BcStackPtr<'v, '_>,
                _ip: BcPtrAddr,
                vs: &Self::Arg,
                _pops: (),
            ) -> Result<[Value<'v>; $n], EvalException> {
                Ok(coerce(*vs))
            }
        }
    };
}

instr_const_n!(2, InstrConst2, InstrConst2Impl, Const2);
instr_const_n!(3, InstrConst3, InstrConst3Impl, Const3);
instr_const_n!(4, InstrConst4, InstrConst4Impl, Const4);

pub(crate) struct InstrLoadLocalImpl;
pub(crate) struct InstrLoadLocalAndConstImpl;
pub(crate) struct InstrLoadLocalCapturedImpl;
pub(crate) struct InstrLoadModuleImpl;
pub(crate) struct InstrStoreLocalImpl;
pub(crate) struct InstrStoreLocalCapturedImpl;
pub(crate) struct InstrStoreModuleImpl;
pub(crate) struct InstrStoreModuleAndExportImpl;
pub(crate) struct InstrUnpackImpl;
pub(crate) struct InstrArrayIndexImpl;
pub(crate) struct InstrArrayIndexNoPopImpl;
pub(crate) struct InstrSetArrayIndexImpl;
pub(crate) struct InstrArrayIndexSetImpl;
pub(crate) struct InstrObjectFieldImpl;
pub(crate) struct InstrSetObjectFieldImpl;
pub(crate) struct InstrObjectSetFieldImpl;
pub(crate) struct InstrSliceImpl;

pub(crate) type InstrLoadLocal = InstrNoFlowAddSpan<InstrLoadLocalImpl>;
pub(crate) type InstrLoadLocalAndConst = InstrNoFlowAddSpan<InstrLoadLocalAndConstImpl>;
pub(crate) type InstrLoadLocalCaptured = InstrNoFlowAddSpan<InstrLoadLocalCapturedImpl>;
pub(crate) type InstrLoadModule = InstrNoFlowAddSpan<InstrLoadModuleImpl>;
pub(crate) type InstrStoreLocal = InstrNoFlow<InstrStoreLocalImpl>;
pub(crate) type InstrStoreLocalCaptured = InstrNoFlow<InstrStoreLocalCapturedImpl>;
pub(crate) type InstrStoreModule = InstrNoFlow<InstrStoreModuleImpl>;
pub(crate) type InstrStoreModuleAndExport = InstrNoFlow<InstrStoreModuleAndExportImpl>;
pub(crate) type InstrUnpack = InstrNoFlowAddSpan<InstrUnpackImpl>;
pub(crate) type InstrArrayIndex = InstrNoFlowAddSpan<InstrArrayIndexImpl>;
pub(crate) type InstrArrayIndexNoPop = InstrNoFlowAddSpan<InstrArrayIndexNoPopImpl>;
pub(crate) type InstrSetArrayIndex = InstrNoFlowAddSpan<InstrSetArrayIndexImpl>;
pub(crate) type InstrArrayIndexSet = InstrNoFlowAddSpan<InstrArrayIndexSetImpl>;
pub(crate) type InstrObjectField = InstrNoFlowAddSpan<InstrObjectFieldImpl>;
pub(crate) type InstrSetObjectField = InstrNoFlowAddSpan<InstrSetObjectFieldImpl>;
pub(crate) type InstrObjectSetField = InstrNoFlowAddSpan<InstrObjectSetFieldImpl>;
pub(crate) type InstrSlice = InstrNoFlowAddSpan<InstrSliceImpl>;

impl InstrNoFlowAddSpanImpl for InstrLoadLocalImpl {
    const OPCODE: BcOpcode = BcOpcode::LoadLocal;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = LocalSlotId;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        arg: &LocalSlotId,
        (): (),
    ) -> Result<Value<'v>, anyhow::Error> {
        eval.get_slot_local(*arg)
    }
}

#[inline(always)]
fn load_local<'v, const N: usize>(
    eval: &mut Evaluator<'v, '_>,
    slots: &[LocalSlotId; N],
    spans: FrozenRef<Vec<Span>>,
) -> Result<[Value<'v>; N], EvalException> {
    #[cold]
    #[inline(never)]
    fn fail<'v>(
        eval: &mut Evaluator<'v, '_>,
        index: usize,
        slot: LocalSlotId,
        spans: FrozenRef<Vec<Span>>,
    ) -> EvalException {
        let err = eval.local_var_referenced_before_assignment(slot);
        let span = spans[index];
        add_span_to_expr_error(err, span, eval)
    }

    let mut values = MaybeUninit::uninit();
    #[allow(clippy::needless_range_loop)]
    for i in 0..N {
        let values: *mut [Value; N] = values.as_mut_ptr();
        let slot = slots[i];
        match eval.local_variables.get_slot(slot) {
            Some(v) => unsafe {
                *(*values).get_unchecked_mut(i) = v;
            },
            None => return Err(fail(eval, i, slot, spans)),
        }
    }
    Ok(unsafe { values.assume_init() })
}

macro_rules! instr_local_local_n {
    ($n:expr, $struct_name:ident, $impl_name:ident, $opcode:ident) => {
        pub(crate) struct $impl_name;
        pub(crate) type $struct_name = InstrNoFlow<$impl_name>;

        impl InstrNoFlowImpl for $impl_name {
            const OPCODE: BcOpcode = BcOpcode::$opcode;
            type Pop<'v> = ();
            type Push<'v> = [Value<'v>; $n];
            type Arg = ([LocalSlotId; $n], FrozenRef<Vec<Span>>);

            #[inline(always)]
            fn run_with_args<'v>(
                eval: &mut Evaluator<'v, '_>,
                _stack: &mut BcStackPtr<'v, '_>,
                _ip: BcPtrAddr,
                (slots, spans): &Self::Arg,
                _pops: (),
            ) -> Result<[Value<'v>; $n], EvalException> {
                load_local(eval, slots, *spans)
            }
        }
    };
}

instr_local_local_n!(2, InstrLoadLocal2, InstrLoadLocal2Impl, LoadLocal2);
instr_local_local_n!(3, InstrLoadLocal3, InstrLoadLocal3Impl, LoadLocal3);
instr_local_local_n!(4, InstrLoadLocal4, InstrLoadLocal4Impl, LoadLocal4);

impl InstrNoFlowAddSpanImpl for InstrLoadLocalAndConstImpl {
    const OPCODE: BcOpcode = BcOpcode::LoadLocalAndConst;
    type Pop<'v> = ();
    type Push<'v> = [Value<'v>; 2];
    type Arg = (LocalSlotId, FrozenValue);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (slot, value): &Self::Arg,
        (): (),
    ) -> Result<[Value<'v>; 2], anyhow::Error> {
        Ok([eval.get_slot_local(*slot)?, value.to_value()])
    }
}

impl InstrNoFlowAddSpanImpl for InstrLoadLocalCapturedImpl {
    const OPCODE: BcOpcode = BcOpcode::LoadLocalCaptured;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = LocalSlotId;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        arg: &LocalSlotId,
        (): (),
    ) -> Result<Value<'v>, anyhow::Error> {
        eval.get_slot_local_captured(*arg)
    }
}

impl InstrNoFlowAddSpanImpl for InstrLoadModuleImpl {
    const OPCODE: BcOpcode = BcOpcode::LoadModule;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = ModuleSlotId;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        arg: &ModuleSlotId,
        (): (),
    ) -> Result<Value<'v>, anyhow::Error> {
        eval.get_slot_module(*arg)
    }
}

impl InstrNoFlowImpl for InstrStoreLocalImpl {
    const OPCODE: BcOpcode = BcOpcode::StoreLocal;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = LocalSlotId;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        arg: &LocalSlotId,
        v: Value<'v>,
    ) -> Result<(), EvalException> {
        eval.set_slot_local(*arg, v);
        Ok(())
    }
}

impl InstrNoFlowImpl for InstrStoreLocalCapturedImpl {
    const OPCODE: BcOpcode = BcOpcode::StoreLocalCaptured;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = LocalSlotId;

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        arg: &LocalSlotId,
        v: Value<'v>,
    ) -> Result<(), EvalException> {
        eval.set_slot_local_captured(*arg, v);
        Ok(())
    }
}

impl InstrNoFlowImpl for InstrStoreModuleAndExportImpl {
    const OPCODE: BcOpcode = BcOpcode::StoreModuleAndExport;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = (ModuleSlotId, String);

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        (slot, name): &(ModuleSlotId, String),
        v: Value<'v>,
    ) -> Result<(), EvalException> {
        v.export_as(name.as_str(), eval);
        eval.set_slot_module(*slot, v);
        Ok(())
    }
}

impl InstrNoFlowImpl for InstrStoreModuleImpl {
    const OPCODE: BcOpcode = BcOpcode::StoreModule;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = ModuleSlotId;

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        slot: &ModuleSlotId,
        v: Value<'v>,
    ) -> Result<(), EvalException> {
        eval.set_slot_module(*slot, v);
        Ok(())
    }
}

impl InstrNoFlowAddSpanImpl for InstrUnpackImpl {
    const OPCODE: BcOpcode = BcOpcode::Unpack;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = ArgPushesStack;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        arg: &Self::Arg,
        v: Value<'v>,
    ) -> Result<(), anyhow::Error> {
        let nvl = v.length()?;
        if nvl != arg.0 as i32 {
            return Err(AssignError::IncorrectNumberOfValueToUnpack(arg.0 as i32, nvl).into());
        }
        let places = stack.push_slice_placeholder(*arg);
        v.with_iterator(eval.heap(), |items| {
            let mut i = 0;
            for item in items {
                // Use unconditional assertion here because we cannot trust
                // user defined `length` and `with_iterator` consistently.
                assert!(i != arg.0 as usize);
                unsafe {
                    (*places.get_unchecked_mut(places.len() - i - 1)).write(item);
                }
                i += 1;
            }
            assert!(i == arg.0 as usize);
        })?;
        Ok(())
    }
}

impl InstrNoFlowAddSpanImpl for InstrArrayIndexImpl {
    const OPCODE: BcOpcode = BcOpcode::ArrayIndex;
    type Pop<'v> = [Value<'v>; 2];
    type Push<'v> = Value<'v>;
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        [array, index]: [Value<'v>; 2],
    ) -> Result<Value<'v>, anyhow::Error> {
        array.at(index, eval.heap())
    }
}

impl InstrNoFlowAddSpanImpl for InstrArrayIndexNoPopImpl {
    const OPCODE: BcOpcode = BcOpcode::ArrayIndexNoPop;
    type Pop<'v> = [Value<'v>; 2];
    type Push<'v> = [Value<'v>; 3];
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        [array, index]: [Value<'v>; 2],
    ) -> Result<[Value<'v>; 3], anyhow::Error> {
        let value = array.at(index, eval.heap())?;
        Ok([array, index, value])
    }
}

impl InstrNoFlowAddSpanImpl for InstrSetArrayIndexImpl {
    const OPCODE: BcOpcode = BcOpcode::SetArrayIndex;
    type Pop<'v> = [Value<'v>; 3];
    type Push<'v> = ();
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        [value, array, index]: [Value<'v>; 3],
    ) -> Result<(), anyhow::Error> {
        array.set_at(index, value)
    }
}

impl InstrNoFlowAddSpanImpl for InstrArrayIndexSetImpl {
    const OPCODE: BcOpcode = BcOpcode::ArrayIndexSet;
    type Pop<'v> = [Value<'v>; 3];
    type Push<'v> = ();
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        [array, index, value]: [Value<'v>; 3],
    ) -> Result<(), anyhow::Error> {
        array.set_at(index, value)
    }
}

impl InstrNoFlowAddSpanImpl for InstrObjectFieldImpl {
    const OPCODE: BcOpcode = BcOpcode::ObjectField;

    type Pop<'v> = Value<'v>;
    type Push<'v> = Value<'v>;
    type Arg = Symbol;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        symbol: &Symbol,
        object: Value<'v>,
    ) -> Result<Value<'v>, anyhow::Error> {
        let (attr_type, v) = get_attr_hashed(object, symbol, eval.heap())?;
        if attr_type == AttrType::Field {
            Ok(v)
        } else if let Some(v_attr) = v.downcast_ref::<NativeAttribute>() {
            v_attr.call(object, eval)
        } else {
            // Insert self so the method see the object it is acting on
            Ok(eval.heap().alloc(BoundMethod::new(object, v)))
        }
    }
}

impl InstrNoFlowAddSpanImpl for InstrSetObjectFieldImpl {
    const OPCODE: BcOpcode = BcOpcode::SetObjectField;

    type Pop<'v> = [Value<'v>; 2];
    type Push<'v> = ();
    type Arg = Symbol;

    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        symbol: &Symbol,
        [v, o]: [Value<'v>; 2],
    ) -> Result<(), anyhow::Error> {
        o.set_attr(symbol.as_str(), v)
    }
}

impl InstrNoFlowAddSpanImpl for InstrObjectSetFieldImpl {
    const OPCODE: BcOpcode = BcOpcode::ObjectSetField;

    type Pop<'v> = [Value<'v>; 2];
    type Push<'v> = ();
    type Arg = Symbol;

    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        symbol: &Symbol,
        [o, v]: [Value<'v>; 2],
    ) -> Result<(), anyhow::Error> {
        o.set_attr(symbol.as_str(), v)
    }
}

impl InstrNoFlowAddSpanImpl for InstrSliceImpl {
    const OPCODE: BcOpcode = BcOpcode::Slice;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (
        ArgPopsStack1,
        ArgPopsStackMaybe1,
        ArgPopsStackMaybe1,
        ArgPopsStackMaybe1,
    );

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (_list, start, stop, step): &Self::Arg,
        (): (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let step = stack.pop_maybe(*step);
        let stop = stack.pop_maybe(*stop);
        let start = stack.pop_maybe(*start);
        let list = stack.pop();

        list.slice(start, stop, step, eval.heap())
    }
}

pub(crate) struct InstrEqImpl;
pub(crate) struct InstrNotEqImpl;

pub(crate) type InstrEq = InstrBinOp<InstrEqImpl>;
pub(crate) type InstrNotEq = InstrBinOp<InstrNotEqImpl>;

impl InstrBinOpImpl for InstrEqImpl {
    const OPCODE: BcOpcode = BcOpcode::Eq;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.equals(v1).map(Value::new_bool)
    }
}

impl InstrBinOpImpl for InstrNotEqImpl {
    const OPCODE: BcOpcode = BcOpcode::NotEq;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.equals(v1).map(|v| Value::new_bool(!v))
    }
}

pub(crate) struct InstrNotImpl;
pub(crate) struct InstrMinusImpl;
pub(crate) struct InstrPlusImpl;
pub(crate) struct InstrBitNotImpl;

pub(crate) type InstrNot = InstrUnOp<InstrNotImpl>;
pub(crate) type InstrMinus = InstrUnOp<InstrMinusImpl>;
pub(crate) type InstrPlus = InstrUnOp<InstrPlusImpl>;
pub(crate) type InstrBitNot = InstrUnOp<InstrBitNotImpl>;

impl InstrUnOpImpl for InstrNotImpl {
    const OPCODE: BcOpcode = BcOpcode::Not;

    #[inline(always)]
    fn eval<'v>(v: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(Value::new_bool(!v.to_bool()))
    }
}

impl InstrUnOpImpl for InstrPlusImpl {
    const OPCODE: BcOpcode = BcOpcode::Plus;

    #[inline(always)]
    fn eval<'v>(v: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v.plus(heap)
    }
}

impl InstrUnOpImpl for InstrMinusImpl {
    const OPCODE: BcOpcode = BcOpcode::Minus;

    #[inline(always)]
    fn eval<'v>(v: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v.minus(heap)
    }
}

impl InstrUnOpImpl for InstrBitNotImpl {
    const OPCODE: BcOpcode = BcOpcode::BitNot;

    #[inline(always)]
    fn eval<'v>(v: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(Value::new_int(!v.to_int()?))
    }
}

pub(crate) trait InstrBinOpImpl: 'static {
    const OPCODE: BcOpcode;

    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error>;
}

pub(crate) trait InstrUnOpImpl: 'static {
    const OPCODE: BcOpcode;

    fn eval<'v>(v: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error>;
}

pub(crate) struct InstrBinOpWrapper<I: InstrBinOpImpl>(marker::PhantomData<I>);
pub(crate) struct InstrUnOpWrapper<I: InstrUnOpImpl>(marker::PhantomData<I>);
pub(crate) type InstrBinOp<I> = InstrNoFlowAddSpan<InstrBinOpWrapper<I>>;
pub(crate) type InstrUnOp<I> = InstrNoFlowAddSpan<InstrUnOpWrapper<I>>;

impl<I: InstrBinOpImpl> InstrNoFlowAddSpanImpl for InstrBinOpWrapper<I> {
    const OPCODE: BcOpcode = I::OPCODE;
    type Pop<'v> = [Value<'v>; 2];
    type Push<'v> = Value<'v>;
    type Arg = ();

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        [v0, v1]: [Value<'v>; 2],
    ) -> Result<Value<'v>, anyhow::Error> {
        I::eval(v0, v1, eval.heap())
    }
}

impl<I: InstrUnOpImpl> InstrNoFlowAddSpanImpl for InstrUnOpWrapper<I> {
    const OPCODE: BcOpcode = I::OPCODE;
    type Pop<'v> = Value<'v>;
    type Push<'v> = Value<'v>;
    type Arg = ();

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        v: Value<'v>,
    ) -> Result<Value<'v>, anyhow::Error> {
        I::eval(v, eval.heap())
    }
}

pub(crate) struct InstrAddImpl;
pub(crate) struct InstrAddAssignImpl;
pub(crate) struct InstrSubImpl;
pub(crate) struct InstrMultiplyImpl;
pub(crate) struct InstrPercentImpl;
pub(crate) struct InstrDivideImpl;
pub(crate) struct InstrFloorDivideImpl;
pub(crate) struct InstrBitAndImpl;
pub(crate) struct InstrBitOrImpl;
pub(crate) struct InstrBitXorImpl;
pub(crate) struct InstrLeftShiftImpl;
pub(crate) struct InstrRightShiftImpl;
pub(crate) struct InstrInImpl;
pub(crate) struct InstrNotInImpl;

pub(crate) type InstrAdd = InstrBinOp<InstrAddImpl>;
pub(crate) type InstrAddAssign = InstrBinOp<InstrAddAssignImpl>;
pub(crate) type InstrSub = InstrBinOp<InstrSubImpl>;
pub(crate) type InstrMultiply = InstrBinOp<InstrMultiplyImpl>;
pub(crate) type InstrPercent = InstrBinOp<InstrPercentImpl>;
pub(crate) type InstrDivide = InstrBinOp<InstrDivideImpl>;
pub(crate) type InstrFloorDivide = InstrBinOp<InstrFloorDivideImpl>;
pub(crate) type InstrBitAnd = InstrBinOp<InstrBitAndImpl>;
pub(crate) type InstrBitOr = InstrBinOp<InstrBitOrImpl>;
pub(crate) type InstrBitXor = InstrBinOp<InstrBitXorImpl>;
pub(crate) type InstrLeftShift = InstrBinOp<InstrLeftShiftImpl>;
pub(crate) type InstrRightShift = InstrBinOp<InstrRightShiftImpl>;
pub(crate) type InstrIn = InstrBinOp<InstrInImpl>;
pub(crate) type InstrNotIn = InstrBinOp<InstrNotInImpl>;

impl InstrBinOpImpl for InstrAddImpl {
    const OPCODE: BcOpcode = BcOpcode::Add;

    #[inline(always)]
    fn eval<'v>(l: Value<'v>, r: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        // Addition of string is super common and pretty cheap, so have a special case for it.
        if let Some(ls) = l.unpack_str() {
            if let Some(rs) = r.unpack_str() {
                if ls.is_empty() {
                    return Ok(r);
                } else if rs.is_empty() {
                    return Ok(l);
                } else {
                    return Ok(heap.alloc_str_concat(ls, rs));
                }
            }
        }

        l.add(r, heap)
    }
}

impl InstrBinOpImpl for InstrAddAssignImpl {
    const OPCODE: BcOpcode = BcOpcode::AddAssign;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        add_assign(v0, v1, heap)
    }
}

impl InstrBinOpImpl for InstrSubImpl {
    const OPCODE: BcOpcode = BcOpcode::Sub;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.sub(v1, heap)
    }
}

impl InstrBinOpImpl for InstrMultiplyImpl {
    const OPCODE: BcOpcode = BcOpcode::Multiply;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.mul(v1, heap)
    }
}

impl InstrBinOpImpl for InstrPercentImpl {
    const OPCODE: BcOpcode = BcOpcode::Percent;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.percent(v1, heap)
    }
}

impl InstrBinOpImpl for InstrFloorDivideImpl {
    const OPCODE: BcOpcode = BcOpcode::FloorDivide;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.floor_div(v1, heap)
    }
}

impl InstrBinOpImpl for InstrDivideImpl {
    const OPCODE: BcOpcode = BcOpcode::Divide;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.div(v1, heap)
    }
}

impl InstrBinOpImpl for InstrBitAndImpl {
    const OPCODE: BcOpcode = BcOpcode::BitAnd;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.bit_and(v1)
    }
}

impl InstrBinOpImpl for InstrBitOrImpl {
    const OPCODE: BcOpcode = BcOpcode::BitOr;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.bit_or(v1)
    }
}

impl InstrBinOpImpl for InstrBitXorImpl {
    const OPCODE: BcOpcode = BcOpcode::BitXor;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.bit_xor(v1)
    }
}

impl InstrBinOpImpl for InstrLeftShiftImpl {
    const OPCODE: BcOpcode = BcOpcode::LeftShift;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.left_shift(v1)
    }
}

impl InstrBinOpImpl for InstrRightShiftImpl {
    const OPCODE: BcOpcode = BcOpcode::RightShift;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        v0.right_shift(v1)
    }
}

impl InstrBinOpImpl for InstrInImpl {
    const OPCODE: BcOpcode = BcOpcode::In;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(Value::new_bool(v1.is_in(v0)?))
    }
}

impl InstrBinOpImpl for InstrNotInImpl {
    const OPCODE: BcOpcode = BcOpcode::NotIn;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(Value::new_bool(!v1.is_in(v0)?))
    }
}

pub(crate) struct InstrPercentSOneImpl;
pub(crate) type InstrPercentSOne = InstrNoFlowAddSpan<InstrPercentSOneImpl>;
pub(crate) struct InstrFormatOneImpl;
pub(crate) type InstrFormatOne = InstrNoFlowAddSpan<InstrFormatOneImpl>;

impl InstrNoFlowAddSpanImpl for InstrPercentSOneImpl {
    const OPCODE: BcOpcode = BcOpcode::PercentSOne;
    type Pop<'v> = Value<'v>;
    type Push<'v> = Value<'v>;
    type Arg = (FrozenStringValue, FrozenStringValue);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (before, after): &Self::Arg,
        arg: Value<'v>,
    ) -> Result<Value<'v>, anyhow::Error> {
        percent_s_one(before.as_str(), arg, after.as_str(), eval.heap())
    }
}

impl InstrNoFlowAddSpanImpl for InstrFormatOneImpl {
    const OPCODE: BcOpcode = BcOpcode::FormatOne;
    type Pop<'v> = Value<'v>;
    type Push<'v> = Value<'v>;
    type Arg = (FrozenStringValue, FrozenStringValue);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (before, after): &Self::Arg,
        arg: Value<'v>,
    ) -> Result<Value<'v>, anyhow::Error> {
        format_one(before.as_str(), arg, after.as_str(), eval.heap())
    }
}

pub(crate) trait InstrCompareImpl: 'static {
    const OPCODE: BcOpcode;
    fn eval_compare(ordering: Ordering) -> bool;
}

pub(crate) struct InstrCompare<I: InstrCompareImpl>(marker::PhantomData<I>);

impl<I: InstrCompareImpl> InstrBinOpImpl for InstrCompare<I> {
    const OPCODE: BcOpcode = I::OPCODE;

    #[inline(always)]
    fn eval<'v>(v0: Value<'v>, v1: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(Value::new_bool(I::eval_compare(v0.compare(v1)?)))
    }
}

pub(crate) struct InstrLessImpl;
pub(crate) struct InstrGreaterImpl;
pub(crate) struct InstrLessOrEqualImpl;
pub(crate) struct InstrGreaterOrEqualImpl;

pub(crate) type InstrLess = InstrBinOp<InstrCompare<InstrLessImpl>>;
pub(crate) type InstrGreater = InstrBinOp<InstrCompare<InstrGreaterImpl>>;
pub(crate) type InstrLessOrEqual = InstrBinOp<InstrCompare<InstrLessOrEqualImpl>>;
pub(crate) type InstrGreaterOrEqual = InstrBinOp<InstrCompare<InstrGreaterOrEqualImpl>>;

impl InstrCompareImpl for InstrLessImpl {
    const OPCODE: BcOpcode = BcOpcode::Less;

    #[inline(always)]
    fn eval_compare(ordering: Ordering) -> bool {
        ordering == Ordering::Less
    }
}

impl InstrCompareImpl for InstrGreaterImpl {
    const OPCODE: BcOpcode = BcOpcode::Greater;

    #[inline(always)]
    fn eval_compare(ordering: Ordering) -> bool {
        ordering == Ordering::Greater
    }
}

impl InstrCompareImpl for InstrLessOrEqualImpl {
    const OPCODE: BcOpcode = BcOpcode::LessOrEqual;

    #[inline(always)]
    fn eval_compare(ordering: Ordering) -> bool {
        ordering != Ordering::Greater
    }
}

impl InstrCompareImpl for InstrGreaterOrEqualImpl {
    const OPCODE: BcOpcode = BcOpcode::GreaterOrEqual;

    #[inline(always)]
    fn eval_compare(ordering: Ordering) -> bool {
        ordering != Ordering::Less
    }
}

pub(crate) struct InstrTypeImpl;
pub(crate) type InstrType = InstrUnOp<InstrTypeImpl>;

impl InstrUnOpImpl for InstrTypeImpl {
    const OPCODE: BcOpcode = BcOpcode::Type;

    #[inline(always)]
    fn eval<'v>(v: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(v.get_type_value().unpack().to_value())
    }
}

pub(crate) struct InstrTypeIsImpl;
pub(crate) type InstrTypeIs = InstrNoFlow<InstrTypeIsImpl>;

impl InstrNoFlowImpl for InstrTypeIsImpl {
    const OPCODE: BcOpcode = BcOpcode::TypeIs;
    type Pop<'v> = Value<'v>;
    type Push<'v> = Value<'v>;
    type Arg = FrozenStringValue;

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        t: &FrozenStringValue,
        v: Value<'v>,
    ) -> Result<Value<'v>, EvalException> {
        Ok(Value::new_bool(v.get_type_value() == *t))
    }
}

pub(crate) struct InstrLenImpl;
pub(crate) type InstrLen = InstrUnOp<InstrLenImpl>;

impl InstrUnOpImpl for InstrLenImpl {
    const OPCODE: BcOpcode = BcOpcode::Len;

    #[inline(always)]
    fn eval<'v>(v: Value<'v>, _heap: &'v Heap) -> Result<Value<'v>, anyhow::Error> {
        Ok(Value::new_int(v.length()?))
    }
}

pub(crate) struct InstrTupleNPopImpl;
pub(crate) struct InstrListNPopImpl;
pub(crate) struct InstrListOfConstsImpl;
pub(crate) struct InstrDictOfConstsImpl;
pub(crate) struct InstrDictConstKeysImpl;
pub(crate) struct InstrDictNPopImpl;
pub(crate) struct InstrListNewImpl;
pub(crate) struct InstrDictNewImpl;
pub(crate) struct InstrComprListAppendImpl;
pub(crate) struct InstrComprDictInsertImpl;

pub(crate) type InstrTupleNPop = InstrNoFlow<InstrTupleNPopImpl>;
pub(crate) type InstrListNew = InstrNoFlow<InstrListNewImpl>;
pub(crate) type InstrListNPop = InstrNoFlow<InstrListNPopImpl>;
pub(crate) type InstrListOfConsts = InstrNoFlow<InstrListOfConstsImpl>;
pub(crate) type InstrDictNew = InstrNoFlow<InstrDictNewImpl>;
pub(crate) type InstrDictOfConsts = InstrNoFlow<InstrDictOfConstsImpl>;
pub(crate) type InstrDictConstKeys = InstrNoFlow<InstrDictConstKeysImpl>;
pub(crate) type InstrDictNPop = InstrNoFlow<InstrDictNPopImpl>;
pub(crate) type InstrComprListAppend = InstrNoFlow<InstrComprListAppendImpl>;
pub(crate) type InstrComprDictInsert = InstrNoFlowAddSpan<InstrComprDictInsertImpl>;

impl InstrNoFlowImpl for InstrTupleNPopImpl {
    const OPCODE: BcOpcode = BcOpcode::TupleNPop;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = ArgPopsStack;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        npops: &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, EvalException> {
        let items = stack.pop_slice(*npops);
        Ok(eval.heap().alloc_tuple(items))
    }
}

impl InstrNoFlowImpl for InstrListNPopImpl {
    const OPCODE: BcOpcode = BcOpcode::ListNPop;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = ArgPopsStack;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        npops: &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, EvalException> {
        let items = stack.pop_slice(*npops);
        Ok(eval.heap().alloc_list(items))
    }
}

impl InstrNoFlowImpl for InstrListOfConstsImpl {
    const OPCODE: BcOpcode = BcOpcode::ListOfConsts;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = Box<[FrozenValue]>;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        values: &Self::Arg,
        (): (),
    ) -> Result<Value<'v>, EvalException> {
        Ok(eval.heap().alloc_list(coerce(&values)))
    }
}

impl InstrNoFlowImpl for InstrDictOfConstsImpl {
    const OPCODE: BcOpcode = BcOpcode::DictOfConsts;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = SmallMap<FrozenValue, FrozenValue>;

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        values: &Self::Arg,
        (): (),
    ) -> Result<Value<'v>, EvalException> {
        Ok(eval.heap().alloc(Dict::new((*coerce(values)).clone())))
    }
}

impl InstrNoFlowImpl for InstrDictNPopImpl {
    const OPCODE: BcOpcode = BcOpcode::DictNPop;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack, FrozenRef<Vec<Span>>);

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        (npops, spans): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, EvalException> {
        let items = stack.pop_slice(*npops);
        debug_assert!(items.len() % 2 == 0);
        debug_assert!(spans.len() == items.len() / 2);
        let mut dict = SmallMap::with_capacity(items.len() / 2);
        for i in 0..items.len() / 2 {
            let k = items[i * 2];
            let v = items[i * 2 + 1];
            let k = match k.get_hashed() {
                Ok(k) => k,
                Err(e) => return Err(add_span_to_expr_error(e, spans[i], eval)),
            };
            let prev = dict.insert_hashed(k, v);
            if prev.is_some() {
                let e = EvalError::DuplicateDictionaryKey(k.key().to_string()).into();
                return Err(add_span_to_expr_error(e, spans[i], eval));
            }
        }
        Ok(eval.heap().alloc(Dict::new(dict)))
    }
}

impl InstrNoFlowImpl for InstrDictConstKeysImpl {
    const OPCODE: BcOpcode = BcOpcode::DictConstKeys;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack, Box<[Hashed<FrozenValue>]>);

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        (npops, keys): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, EvalException> {
        let values = stack.pop_slice(*npops);
        assert!(keys.len() == values.len());
        let mut dict = SmallMap::with_capacity(keys.len());
        for (k, v) in keys.iter().zip(values) {
            let prev = dict.insert_hashed(*k, *v);
            debug_assert!(prev.is_none());
        }
        Ok(eval.heap().alloc(Dict::new(coerce(dict))))
    }
}

impl InstrNoFlowImpl for InstrListNewImpl {
    const OPCODE: BcOpcode = BcOpcode::ListNew;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        (): &(),
        (): (),
    ) -> Result<Value<'v>, EvalException> {
        Ok(eval.heap().alloc_list(&[]))
    }
}

impl InstrNoFlowImpl for InstrDictNewImpl {
    const OPCODE: BcOpcode = BcOpcode::DictNew;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        (): &(),
        (): (),
    ) -> Result<Value<'v>, EvalException> {
        Ok(eval.heap().alloc(Dict::default()))
    }
}

impl InstrNoFlowImpl for InstrComprListAppendImpl {
    const OPCODE: BcOpcode = BcOpcode::ComprListAppend;
    type Pop<'v> = [Value<'v>; 2];
    type Push<'v> = Value<'v>;
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        (): &(),
        [list, item]: [Value<'v>; 2],
    ) -> Result<Value<'v>, EvalException> {
        List::from_value_mut(list)
            .unwrap()
            .unwrap()
            .push(item, eval.heap());
        Ok(list)
    }
}

impl InstrNoFlowAddSpanImpl for InstrComprDictInsertImpl {
    const OPCODE: BcOpcode = BcOpcode::ComprDictInsert;
    type Pop<'v> = [Value<'v>; 3];
    type Push<'v> = Value<'v>;
    type Arg = ();

    #[inline(always)]
    fn run_with_args<'v>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        (): &(),
        [dict, key, value]: [Value<'v>; 3],
    ) -> Result<Value<'v>, anyhow::Error> {
        let key = key.get_hashed()?;
        Dict::from_value_mut(dict)
            .unwrap()
            .unwrap()
            .insert_hashed(key, value);
        Ok(dict)
    }
}

pub(crate) struct InstrBr;
pub(crate) struct InstrIfBr;
pub(crate) struct InstrIfNotBr;

impl BcInstr for InstrBr {
    const OPCODE: BcOpcode = BcOpcode::Br;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = BcAddrOffset;

    #[inline(always)]
    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr<'b>,
        target: &BcAddrOffset,
    ) -> InstrControl<'v, 'b> {
        InstrControl::Next(ip.add_rel(*target))
    }
}

impl BcInstr for InstrIfBr {
    const OPCODE: BcOpcode = BcOpcode::IfBr;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = BcAddrOffset;

    #[inline(always)]
    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr<'b>,
        target: &BcAddrOffset,
    ) -> InstrControl<'v, 'b> {
        let cond = stack.pop();
        if cond.to_bool() {
            InstrControl::Next(ip.add_rel(*target))
        } else {
            InstrControl::Next(ip.add_instr::<Self>())
        }
    }
}

impl BcInstr for InstrIfNotBr {
    const OPCODE: BcOpcode = BcOpcode::IfNotBr;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = BcAddrOffset;

    #[inline(always)]
    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr<'b>,
        target: &BcAddrOffset,
    ) -> InstrControl<'v, 'b> {
        let cond = stack.pop();
        if !cond.to_bool() {
            InstrControl::Next(ip.add_rel(*target))
        } else {
            InstrControl::Next(ip.add_instr::<Self>())
        }
    }
}

pub(crate) struct InstrForLoop;
pub(crate) struct InstrBreak;
pub(crate) struct InstrContinue;

impl BcInstr for InstrForLoop {
    const OPCODE: BcOpcode = BcOpcode::ForLoop;
    type Pop<'v> = Value<'v>;
    type Push<'v> = Value<'v>;
    type Arg = BcAddrOffset;

    fn run<'v, 'b>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        ip: BcPtrAddr<'b>,
        loop_end: &BcAddrOffset,
    ) -> InstrControl<'v, 'b> {
        let ss = stack.stack_offset();

        let collection = stack.pop();

        enum LoopResult<'v> {
            Ok,
            Return(Value<'v>),
            Err(EvalException),
        }

        let iter_ret = collection.with_iterator(eval.heap(), |iter| {
            let loop_start = ip.add_instr::<Self>();
            for item in iter {
                stack.push(item);
                debug_assert!(stack.stack_offset() == ss);
                match run_block(eval, stack, loop_start) {
                    RunBlockResult::Continue => {}
                    RunBlockResult::Break => return LoopResult::Ok,
                    RunBlockResult::Return(v) => return LoopResult::Return(v),
                    RunBlockResult::Err(e) => return LoopResult::Err(e),
                }
            }
            LoopResult::Ok
        });
        match iter_ret {
            Ok(LoopResult::Ok) => {
                debug_assert!(stack.stack_offset() + 1 == ss);
                InstrControl::Next(ip.add_rel(*loop_end))
            }
            Ok(LoopResult::Return(v)) => {
                debug_assert!(stack.stack_offset() + 1 == ss);
                InstrControl::Return(v)
            }
            Ok(LoopResult::Err(e)) => InstrControl::Err(e),
            Err(e) => InstrControl::Err(Bc::wrap_error_for_instr_ptr(ip, e, eval)),
        }
    }
}

impl BcInstr for InstrBreak {
    const OPCODE: BcOpcode = BcOpcode::Break;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = ();

    #[inline(always)]
    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr<'b>,
        (): &(),
    ) -> InstrControl<'v, 'b> {
        InstrControl::LoopBreak
    }
}

impl BcInstr for InstrContinue {
    const OPCODE: BcOpcode = BcOpcode::Continue;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = ();

    #[inline(always)]
    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr<'b>,
        (): &(),
    ) -> InstrControl<'v, 'b> {
        InstrControl::LoopContinue
    }
}

pub(crate) struct InstrReturnNone;
pub(crate) struct InstrReturn;

impl BcInstr for InstrReturnNone {
    const OPCODE: BcOpcode = BcOpcode::ReturnNone;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = ();

    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr<'b>,
        (): &(),
    ) -> InstrControl<'v, 'b> {
        InstrControl::Return(Value::new_none())
    }
}

impl BcInstr for InstrReturn {
    const OPCODE: BcOpcode = BcOpcode::Return;
    type Pop<'v> = Value<'v>;
    type Push<'v> = ();
    type Arg = ();

    #[inline(always)]
    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr<'b>,
        (): &(),
    ) -> InstrControl<'v, 'b> {
        let v = stack.pop();
        InstrControl::Return(v)
    }
}

pub(crate) struct InstrDefImpl;
pub(crate) type InstrDef = InstrNoFlow<InstrDefImpl>;

#[derive(Debug)]
pub(crate) struct InstrDefData {
    pub(crate) function_name: String,
    pub(crate) params: Vec<Spanned<ParameterCompiled<u32>>>,
    pub(crate) return_type: Option<Spanned<u32>>,
    pub(crate) info: FrozenRef<DefInfo>,
}

impl InstrNoFlowImpl for InstrDefImpl {
    const OPCODE: BcOpcode = BcOpcode::Def;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack, InstrDefData);

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        (pops, def_data): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, EvalException> {
        let pop = stack.pop_slice(*pops);

        let mut parameters =
            ParametersSpec::with_capacity(def_data.function_name.clone(), def_data.params.len());
        let mut parameter_types = Vec::new();
        let mut parameter_captures = Vec::new();

        let mut pop_index = 0;

        // count here rather than enumerate because '*' doesn't get a real
        // index in the parameter mapping, and it messes up the indexes
        let mut i = 0;
        for x in &def_data.params {
            if let Some(t) = x.ty() {
                assert!(*t == pop_index);
                let v = pop[pop_index as usize];
                pop_index += 1;
                let name = x.name().unwrap_or("unknown").to_owned();
                parameter_types.push((
                    i,
                    name,
                    v,
                    expr_throw(TypeCompiled::new(v, eval.heap()), x.span, eval)?,
                ));
            }
            match &x.node {
                ParameterCompiled::Normal(n, _) => parameters.required(&n.name),
                ParameterCompiled::WithDefaultValue(n, ty, v) => {
                    assert!(*v == pop_index);
                    let value = pop[pop_index as usize];
                    pop_index += 1;

                    if ty.is_some() {
                        // Check the type of the default
                        let (_, _, ty_value, ty_compiled) = parameter_types.last().unwrap();
                        expr_throw(
                            value.check_type_compiled(*ty_value, ty_compiled, Some(&n.name)),
                            x.span,
                            eval,
                        )?;
                    }
                    parameters.defaulted(&n.name, value);
                }
                ParameterCompiled::NoArgs => parameters.no_args(),
                ParameterCompiled::Args(_, _) => parameters.args(),
                ParameterCompiled::KwArgs(_, _) => parameters.kwargs(),
            };
            if let Captured::Yes = x.captured() {
                parameter_captures.push(i);
            }
            if !matches!(x.node, ParameterCompiled::NoArgs) {
                i += 1;
            }
        }
        let return_type = match &def_data.return_type {
            None => None,
            Some(v) => {
                assert!(v.node == pop_index);
                let value = pop[pop_index as usize];
                pop_index += 1;
                Some((
                    value,
                    expr_throw(TypeCompiled::new(value, eval.heap()), v.span, eval)?,
                ))
            }
        };
        assert!(pop_index as usize == pop.len());
        Ok(eval.heap().alloc(Def::new(
            parameters,
            parameter_captures,
            parameter_types,
            return_type,
            def_data.info,
            eval,
        )))
    }
}

pub(crate) struct InstrCallImpl;
pub(crate) struct InstrCallPosImpl;
pub(crate) struct InstrCallFrozenDefImpl;
pub(crate) struct InstrCallFrozenDefPosImpl;
pub(crate) struct InstrCallFrozenNativeImpl;
pub(crate) struct InstrCallFrozenNativePosImpl;
pub(crate) struct InstrCallFrozenImpl;
pub(crate) struct InstrCallFrozenPosImpl;
pub(crate) struct InstrCallMethodImpl;
pub(crate) struct InstrCallMethodPosImpl;

pub(crate) type InstrCall = InstrNoFlowAddSpan<InstrCallImpl>;
pub(crate) type InstrCallPos = InstrNoFlowAddSpan<InstrCallPosImpl>;
pub(crate) type InstrCallFrozenDef = InstrNoFlowAddSpan<InstrCallFrozenDefImpl>;
pub(crate) type InstrCallFrozenDefPos = InstrNoFlowAddSpan<InstrCallFrozenDefPosImpl>;
pub(crate) type InstrCallFrozenNative = InstrNoFlowAddSpan<InstrCallFrozenNativeImpl>;
pub(crate) type InstrCallFrozenNativePos = InstrNoFlowAddSpan<InstrCallFrozenNativePosImpl>;
pub(crate) type InstrCallFrozen = InstrNoFlowAddSpan<InstrCallFrozenImpl>;
pub(crate) type InstrCallFrozenPos = InstrNoFlowAddSpan<InstrCallFrozenPosImpl>;
pub(crate) type InstrCallMethod = InstrNoFlowAddSpan<InstrCallMethodImpl>;
pub(crate) type InstrCallMethodPos = InstrNoFlowAddSpan<InstrCallMethodPosImpl>;

impl InstrNoFlowAddSpanImpl for InstrCallImpl {
    const OPCODE: BcOpcode = BcOpcode::Call;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack1, ArgsCompiledValueBc);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (_pop1, args): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let arguments = stack.pop_args(args);
        let f = stack.pop();
        f.invoke(Some(args.span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallPosImpl {
    const OPCODE: BcOpcode = BcOpcode::CallPos;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack1, ArgPopsStack, Span);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (_pop1, npops, span): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let arguments = stack.pop_args_pos(*npops);
        let f = stack.pop();
        f.invoke(Some(*span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallFrozenDefImpl {
    const OPCODE: BcOpcode = BcOpcode::CallFrozenDef;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (FrozenValueTyped<'static, FrozenDef>, ArgsCompiledValueBc);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (fun, args): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let arguments = stack.pop_args(args);
        fun.as_ref()
            .invoke(fun.to_value(), Some(args.span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallFrozenDefPosImpl {
    const OPCODE: BcOpcode = BcOpcode::CallFrozenDefPos;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack, FrozenValueTyped<'static, FrozenDef>, Span);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (npops, fun, span): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let arguments = stack.pop_args_pos(*npops);
        fun.as_ref()
            .invoke(fun.to_value(), Some(*span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallFrozenNativeImpl {
    const OPCODE: BcOpcode = BcOpcode::CallFrozenNative;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (
        Option<FrozenValue>,
        FrozenValueTyped<'static, NativeFunction>,
        ArgsCompiledValueBc,
    );

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (this, fun, args): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let mut arguments = stack.pop_args(args);
        arguments.this = this.map(|v| v.to_value());
        fun.as_ref()
            .invoke(fun.to_value(), Some(args.span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallFrozenNativePosImpl {
    const OPCODE: BcOpcode = BcOpcode::CallFrozenNativePos;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (
        ArgPopsStack,
        Option<FrozenValue>,
        FrozenValueTyped<'static, NativeFunction>,
        Span,
    );

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (npops, this, fun, span): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let mut arguments = stack.pop_args_pos(*npops);
        arguments.this = this.map(|v| v.to_value());
        fun.as_ref()
            .invoke(fun.to_value(), Some(*span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallFrozenImpl {
    const OPCODE: BcOpcode = BcOpcode::CallFrozen;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (Option<FrozenValue>, FrozenValue, ArgsCompiledValueBc);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (this, fun, args): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let mut arguments = stack.pop_args(args);
        arguments.this = this.map(|v| v.to_value());
        fun.invoke(Some(args.span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallFrozenPosImpl {
    const OPCODE: BcOpcode = BcOpcode::CallFrozenPos;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack, Option<FrozenValue>, FrozenValue, Span);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (npops, this, fun, span): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let mut arguments = stack.pop_args_pos(*npops);
        arguments.this = this.map(|v| v.to_value());
        fun.invoke(Some(*span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallMethodImpl {
    const OPCODE: BcOpcode = BcOpcode::CallMethod;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack1, Symbol, ArgsCompiledValueBc);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (_pop1, symbol, args): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let mut arguments = stack.pop_args(args);
        let this = stack.pop();
        arguments.this = Some(this);
        // TODO: wrong span: should be span of `object.method`, not of the whole expression
        let fun = get_attr_hashed(this, symbol, eval.heap())?.1;
        fun.invoke(Some(args.span), arguments, eval)
    }
}

impl InstrNoFlowAddSpanImpl for InstrCallMethodPosImpl {
    const OPCODE: BcOpcode = BcOpcode::CallMethodPos;
    type Pop<'v> = ();
    type Push<'v> = Value<'v>;
    type Arg = (ArgPopsStack1, ArgPopsStack, Symbol, Span);

    #[inline(always)]
    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        stack: &mut BcStackPtr<'v, '_>,
        (_pop1, npops, symbol, span): &Self::Arg,
        _pops: (),
    ) -> Result<Value<'v>, anyhow::Error> {
        let mut arguments = stack.pop_args_pos(*npops);
        let this = stack.pop();
        arguments.this = Some(this);
        // TODO: wrong span: should be span of `object.method`, not of the whole expression
        let fun = get_attr_hashed(this, symbol, eval.heap())?.1;
        fun.invoke(Some(*span), arguments, eval)
    }
}

pub(crate) struct InstrPossibleGcImpl;
pub(crate) struct InstrBeforeStmtImpl;
pub(crate) struct InstrProfileBcImpl;

pub(crate) type InstrPossibleGc = InstrNoFlow<InstrPossibleGcImpl>;
pub(crate) type InstrBeforeStmt = InstrNoFlow<InstrBeforeStmtImpl>;
pub(crate) type InstrProfileBc = InstrNoFlow<InstrProfileBcImpl>;

impl InstrNoFlowImpl for InstrPossibleGcImpl {
    const OPCODE: BcOpcode = BcOpcode::PossibleGc;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = ();

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        (): &(),
        (): (),
    ) -> Result<(), EvalException> {
        possible_gc(eval);
        Ok(())
    }
}

impl InstrNoFlowImpl for InstrBeforeStmtImpl {
    const OPCODE: BcOpcode = BcOpcode::BeforeStmt;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = Span;

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _: BcPtrAddr,
        span: &Span,
        (): (),
    ) -> Result<(), EvalException> {
        before_stmt(*span, eval);
        Ok(())
    }
}

impl InstrNoFlowImpl for InstrProfileBcImpl {
    const OPCODE: BcOpcode = BcOpcode::ProfileBc;
    type Pop<'v> = ();
    type Push<'v> = ();
    type Arg = BcOpcode;

    fn run_with_args<'v>(
        eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr,
        opcode: &BcOpcode,
        (): (),
    ) -> Result<(), EvalException> {
        eval.bc_profile.before_instr(*opcode);
        Ok(())
    }
}

/// Pseudo-instruction:
/// * to store bytecode metadata (i.e. spans): when bytecode is evaluated, we only have IP,
///   we don't have a pointer to bytecode object. To obtain spans by IP, we scroll
///   through the instruction until we encounter this pseudo-instruction.
/// * as a safety against memory overruns. Function block must terminate with return instruction,
///  but if return was missed, this instruction is executed and it panics.
pub(crate) struct InstrEndOfBc;

impl BcInstr for InstrEndOfBc {
    const OPCODE: BcOpcode = BcOpcode::EndOfBc;
    type Pop<'v> = ();
    type Push<'v> = ();
    /// Offset of current instruction and spans of all instructions.
    type Arg = (BcAddr, Vec<(BcAddr, Span)>);

    fn run<'v, 'b>(
        _eval: &mut Evaluator<'v, '_>,
        _stack: &mut BcStackPtr<'v, '_>,
        _ip: BcPtrAddr<'b>,
        (_this_instr_offset, _spans): &Self::Arg,
    ) -> InstrControl<'v, 'b> {
        unreachable!("this instruction is not meant to be executed");
    }
}
