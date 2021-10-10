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

use crate::{
    codemap::{Span, Spanned},
    eval::{
        bc::{
            bytecode::Bc,
            instr_impl::{
                InstrBeforeStmt, InstrBreak, InstrContinue, InstrPossibleGc, InstrReturn,
                InstrReturnNone,
            },
            writer::BcWriter,
        },
        fragment::{
            expr::{ExprCompiledValue, MaybeNot},
            stmt::{StmtCompileContext, StmtCompiledValue, StmtsCompiled},
        },
    },
};

impl StmtsCompiled {
    pub(crate) fn write_bc(&self, compiler: &StmtCompileContext, bc: &mut BcWriter) {
        for stmt in self.stmts() {
            stmt.write_bc(compiler, bc);
        }
    }
}

impl Spanned<StmtCompiledValue> {
    fn write_bc(&self, compiler: &StmtCompileContext, bc: &mut BcWriter) {
        assert_eq!(bc.stack_size(), 0);
        if compiler.has_before_stmt {
            match self.node {
                StmtCompiledValue::PossibleGc => {}
                _ => bc.write_instr::<InstrBeforeStmt>(self.span, self.span),
            }
        }
        self.write_bc_inner(compiler, bc);
        assert_eq!(
            bc.stack_size(),
            0,
            "stack size must be zero after writing {:?}",
            self.node
        );
    }

    fn write_if_then(
        compiler: &StmtCompileContext,
        bc: &mut BcWriter,
        c: &Spanned<ExprCompiledValue>,
        maybe_not: MaybeNot,
        t: &dyn Fn(&StmtCompileContext, &mut BcWriter),
    ) {
        if let ExprCompiledValue::Not(box ref c) = c.node {
            Self::write_if_then(compiler, bc, c, maybe_not.negate(), t);
        } else if let (ExprCompiledValue::And(box (ref a, ref b)), MaybeNot::Id) =
            (&c.node, maybe_not)
        {
            // `if a and b`
            //  |||
            // `if a: if b:
            Self::write_if_then(compiler, bc, a, MaybeNot::Id, &|compiler, bc| {
                Self::write_if_then(compiler, bc, b, MaybeNot::Id, t);
            });
        } else if let (ExprCompiledValue::Or(box (ref a, ref b)), MaybeNot::Not) =
            (&c.node, maybe_not)
        {
            // `if not (a or b)`
            //  |||
            // `if (not a) and (not b)`
            Self::write_if_then(compiler, bc, a, MaybeNot::Not, &|compiler, bc| {
                Self::write_if_then(compiler, bc, b, MaybeNot::Not, t);
            });
        } else {
            // TODO: handle more and and or
            match maybe_not {
                MaybeNot::Id => {
                    c.write_bc(bc);
                    bc.write_if(c.span, |bc| {
                        t(compiler, bc);
                    })
                }
                MaybeNot::Not => {
                    c.write_bc(bc);
                    bc.write_if_not(c.span, |bc| {
                        t(compiler, bc);
                    })
                }
            }
        }
    }

    fn write_if_else(
        c: &Spanned<ExprCompiledValue>,
        maybe_not: MaybeNot,
        t: &StmtsCompiled,
        f: &StmtsCompiled,
        compiler: &StmtCompileContext,
        bc: &mut BcWriter,
    ) {
        assert!(!t.is_empty() || !f.is_empty());
        if f.is_empty() {
            Self::write_if_then(compiler, bc, c, maybe_not, &|compiler, bc| {
                t.write_bc(compiler, bc)
            });
        } else if t.is_empty() {
            Self::write_if_then(compiler, bc, c, maybe_not.negate(), &|compiler, bc| {
                f.write_bc(compiler, bc)
            });
        } else if let ExprCompiledValue::Not(box ref c) = c.node {
            Self::write_if_else(c, maybe_not.negate(), f, t, compiler, bc);
        } else {
            // TODO: handle and and or
            c.write_bc(bc);
            bc.write_if_else(
                c.span,
                |bc| t.write_bc(compiler, bc),
                |bc| f.write_bc(compiler, bc),
            );
        }
    }

    fn write_bc_inner(&self, compiler: &StmtCompileContext, bc: &mut BcWriter) {
        let span = self.span;
        match self.node {
            StmtCompiledValue::PossibleGc => bc.write_instr::<InstrPossibleGc>(span, ()),
            StmtCompiledValue::Return(None) => {
                bc.write_instr::<InstrReturnNone>(span, ());
            }
            StmtCompiledValue::Return(Some(ref expr)) => {
                expr.write_bc(bc);
                bc.write_instr::<InstrReturn>(span, ());
            }
            StmtCompiledValue::Expr(ref expr) => {
                expr.write_bc_for_effect(bc);
            }
            StmtCompiledValue::Assign(ref lhs, ref rhs) => {
                rhs.write_bc(bc);
                lhs.write_bc(bc);
            }
            StmtCompiledValue::AssignModify(ref lhs, op, ref rhs) => {
                lhs.write_bc(span, op, rhs, bc);
            }
            StmtCompiledValue::If(box (ref c, ref t, ref f)) => {
                Self::write_if_else(c, MaybeNot::Id, t, f, compiler, bc);
            }
            StmtCompiledValue::For(box (ref assign, ref over, ref body)) => {
                over.write_bc(bc);
                bc.write_for(span, |bc| {
                    assign.write_bc(bc);
                    body.write_bc(compiler, bc);
                });
            }
            StmtCompiledValue::Break => {
                bc.write_instr::<InstrBreak>(span, ());
            }
            StmtCompiledValue::Continue => {
                bc.write_instr::<InstrContinue>(span, ());
            }
        }
    }
}

impl StmtsCompiled {
    pub(crate) fn as_bc(&self, compiler: &StmtCompileContext) -> Bc {
        let mut bc = BcWriter::new();
        self.write_bc(compiler, &mut bc);
        bc.write_instr::<InstrReturnNone>(Span::default(), ());
        bc.finish()
    }
}
