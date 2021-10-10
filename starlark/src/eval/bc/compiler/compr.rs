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

//! Compile comprehensions.

use crate::{
    codemap::Span,
    eval::{
        bc::{
            instr_impl::{
                InstrComprDictInsert, InstrComprListAppend, InstrContinue, InstrDictNew,
                InstrListNew,
            },
            writer::BcWriter,
        },
        fragment::compr::{ClauseCompiled, ComprCompiled},
    },
};

impl ClauseCompiled {
    fn write_bc(
        &self,
        bc: &mut BcWriter,
        rem: &[ClauseCompiled],
        term: impl FnOnce(&mut BcWriter),
    ) {
        self.over.write_bc(bc);
        bc.write_for(self.over_span, |bc| {
            self.var.write_bc(bc);
            for c in &self.ifs {
                c.write_bc(bc);
                bc.write_if_not(c.span, |bc| {
                    bc.write_instr::<InstrContinue>(c.span, ());
                });
            }

            match rem.split_last() {
                Some((first, rem)) => {
                    first.write_bc(bc, rem, term);
                }
                None => {
                    term(bc);
                }
            }
        })
    }
}

impl ComprCompiled {
    pub(crate) fn write_bc(&self, span: Span, bc: &mut BcWriter) {
        let ss = bc.stack_size();
        match *self {
            ComprCompiled::List(box ref expr, ref clauses) => {
                bc.write_instr::<InstrListNew>(span, ());
                let (first, rem) = clauses.split_last().unwrap();
                first.write_bc(bc, rem, |bc| {
                    expr.write_bc(bc);
                    bc.write_instr::<InstrComprListAppend>(expr.span, ());
                });
            }
            ComprCompiled::Dict(box (ref k, ref v), ref clauses) => {
                bc.write_instr::<InstrDictNew>(span, ());
                let (first, rem) = clauses.split_last().unwrap();
                first.write_bc(bc, rem, |bc| {
                    k.write_bc(bc);
                    v.write_bc(bc);
                    bc.write_instr::<InstrComprDictInsert>(k.span, ());
                });
            }
        };
        assert!(
            bc.stack_size() == ss + 1,
            "Compilation of comprehension must produce one value on the stack"
        );
    }
}
