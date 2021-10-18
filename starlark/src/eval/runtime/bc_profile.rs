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

// For `#[allow(gazebo_impl_dupe)]`.
#![allow(unknown_lints)]

//! Bytecode profiler.

use std::{
    fs,
    path::Path,
    time::{Duration, Instant},
};

use crate::eval::{
    bc::opcode::BcOpcode,
    runtime::{csv::CsvWriter, evaluator::EvaluatorError},
};

// TODO(nga): `Dupe` for `Duration` added in D31723072, need to release gazebo to use it.
#[allow(gazebo_impl_dupe)]
#[derive(Default, Clone, Copy)]
struct BcInstrStat {
    count: u64,
    total_time: Duration,
}

impl BcInstrStat {
    fn avg_time(&self) -> Duration {
        if self.count == 0 {
            Duration::ZERO
        } else {
            Duration::from_nanos(self.total_time.as_nanos() as u64 / self.count)
        }
    }
}

struct BcProfileData {
    last: Option<(BcOpcode, Instant)>,
    by_instr: [BcInstrStat; BcOpcode::COUNT],
}

// Derive doesn't work here.
impl Default for BcProfileData {
    fn default() -> Self {
        BcProfileData {
            last: None,
            by_instr: [BcInstrStat::default(); BcOpcode::COUNT],
        }
    }
}

impl BcProfileData {
    fn write_csv(&self, path: &Path) -> anyhow::Result<()> {
        fs::write(path, self.gen_csv().as_bytes())?;
        Ok(())
    }

    fn gen_csv(&self) -> String {
        let mut by_instr: Vec<_> = self
            .by_instr
            .iter()
            .enumerate()
            .map(|(i, st)| (BcOpcode::by_number(i as u32).unwrap(), st))
            .collect();
        by_instr.sort_by_key(|(_opcode, st)| u64::MAX - st.count);
        let mut csv = CsvWriter::new(["Opcode", "Count", "Total time (s)", "Avg time (ns)"]);
        for (opcode, instr_stats) in &by_instr {
            csv.write_debug(opcode);
            csv.write_value(instr_stats.count);
            csv.write_value(instr_stats.total_time);
            csv.write_value(instr_stats.avg_time().as_nanos());
            csv.finish_row();
        }
        csv.finish()
    }
}

pub(crate) struct BcProfile {
    data: Option<Box<BcProfileData>>,
}

impl BcProfile {
    pub(crate) fn new() -> BcProfile {
        BcProfile { data: None }
    }

    pub(crate) fn enable(&mut self) {
        self.data = Some(Default::default());
    }

    pub(crate) fn enabled(&self) -> bool {
        self.data.is_some()
    }

    pub(crate) fn write_csv(&self, path: &Path) -> anyhow::Result<()> {
        match self.data {
            Some(ref data) => data.write_csv(path),
            None => Err(EvaluatorError::BcProfilingNotEnabled.into()),
        }
    }

    /// Called from bytecode.
    pub(crate) fn before_instr(&mut self, opcode: BcOpcode) {
        let data = self.data.as_mut().expect("enabled but not enabled");

        let now = Instant::now();
        if let Some((last_opcode, last_time)) = data.last {
            let last_duration = now.saturating_duration_since(last_time);
            data.by_instr[last_opcode as usize].count += 1;
            data.by_instr[last_opcode as usize].total_time += last_duration;
        }
        data.last = Some((opcode, now));
    }
}

#[cfg(test)]
mod test {
    use crate::{
        environment::{Globals, Module},
        eval::{bc::opcode::BcOpcode, Evaluator},
        syntax::{AstModule, Dialect},
    };

    #[test]
    fn test_smoke() {
        let module = Module::new();
        let globals = Globals::standard();
        let mut eval = Evaluator::new(&module, &globals);
        eval.enable_bc_profile();
        eval.eval_module(
            AstModule::parse("bc.star", "repr([1, 2])".to_owned(), &Dialect::Standard).unwrap(),
        )
        .unwrap();
        let csv = eval.bc_profile.data.as_mut().unwrap().gen_csv();
        assert!(
            csv.contains(&format!("\n{:?},1,", BcOpcode::CallFrozenNativePos)),
            "{:?}",
            csv
        );
    }
}
