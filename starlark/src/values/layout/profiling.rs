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

use crate::values::{
    layout::{heap::Heap, value::ValueMem},
    Value,
};
use anyhow::Context;
use gazebo::prelude::*;
use regex::Regex;
use std::{
    collections::{hash_map::Entry, HashMap},
    fs::File,
    io,
    io::Write,
    path::Path,
    time::{Duration, Instant},
};

#[derive(Copy, Clone, Dupe, Debug, Eq, PartialEq, Hash)]
struct FunctionId(usize);

/// A mapping from function Value to FunctionId, which must be continuous
#[derive(Default)]
struct FunctionIds {
    // The usize is the result of ptr_value()
    values: HashMap<usize, FunctionId>,
    strings: HashMap<String, FunctionId>,
}

impl FunctionIds {
    fn get_string(&mut self, x: String) -> FunctionId {
        let next = FunctionId(self.strings.len());
        match self.strings.entry(x) {
            Entry::Occupied(inner) => *inner.get(),
            Entry::Vacant(inner) => {
                inner.insert(next);
                next
            }
        }
    }

    fn get_value(&mut self, x: Value) -> FunctionId {
        let next = FunctionId(self.strings.len());
        match self.values.entry(x.ptr_value()) {
            Entry::Occupied(v) => *v.get(),
            Entry::Vacant(outer) => {
                let s = x.to_str();
                match self.strings.entry(s) {
                    Entry::Occupied(inner) => {
                        let res = *inner.get();
                        outer.insert(res);
                        res
                    }
                    Entry::Vacant(inner) => {
                        inner.insert(next);
                        outer.insert(next);
                        next
                    }
                }
            }
        }
    }

    fn invert(&self) -> Vec<&str> {
        let mut res = vec![""; self.strings.len()];
        for (name, id) in &self.strings {
            res[id.0] = name.as_str();
        }
        res
    }
}

/// Information relating to a function.
#[derive(Default, Debug, Clone)]
struct FuncInfo {
    /// Number of times this function was called
    calls: usize,
    /// Who called this function (and how many times each)
    callers: HashMap<FunctionId, usize>,
    /// Time spent directly in this function
    time: Duration,
    /// Time spent directly in this function and recursive functions.
    time_rec: Duration,
    /// Allocations made by this function
    allocs: HashMap<&'static str, usize>,
}

impl FuncInfo {
    fn merge<'a>(xs: impl Iterator<Item = &'a Self>) -> Self {
        let mut result = Self::default();
        for x in xs {
            result.calls += x.calls;
            result.time += x.time;
            for (k, v) in x.allocs.iter() {
                *result.allocs.entry(k).or_insert(0) += v;
            }
        }
        // Recursive time doesn't accumulate nicely, the time is the right value
        result.time_rec = result.time;
        result
    }
}

/// We morally have two pieces of information:
/// 1. Information about each function.
/// 2. The call stack.
///
/// However, we are always updating the top of the call stack,
/// so pull out top_stack/top_info as a cache.
struct Info {
    ids: FunctionIds,

    /// Information about all functions
    info: Vec<FuncInfo>,
    /// When the top of the stack last changed
    last_changed: Instant,
    /// Each entry is (Function, time_rec when I started, time I started)
    /// The time_rec is recorded so that recursion doesn't screw up time_rec
    call_stack: Vec<(FunctionId, Duration, Instant)>,
}

impl Info {
    fn ensure(&mut self, x: FunctionId) {
        if self.info.len() <= x.0 {
            self.info.resize(x.0 + 1, FuncInfo::default());
        }
    }

    fn top_id(&self) -> FunctionId {
        self.call_stack.last().unwrap().0
    }

    fn top_info(&mut self) -> &mut FuncInfo {
        let top = self.top_id();
        &mut self.info[top.0]
    }

    /// Called before you change the top of the stack
    fn change(&mut self, now: Instant) {
        let start = self.last_changed;
        self.top_info().time += now.checked_duration_since(start).unwrap_or_default();
        self.last_changed = now;
    }

    /// Process each ValueMem in their chronological order
    fn process<'v>(&mut self, x: &'v ValueMem<'v>) {
        match x {
            ValueMem::CallEnter(function, now) => {
                let id = self.ids.get_value(*function);
                self.ensure(id);
                self.change(*now);

                let top = self.top_id();
                let mut me = &mut self.info[id.0];
                me.calls += 1;
                *me.callers.entry(top).or_insert(0) += 1;
                self.call_stack.push((id, me.time_rec, *now));
            }
            ValueMem::CallExit(now) => {
                self.change(*now);
                let (name, time_rec, start) = self.call_stack.pop().unwrap();
                self.info[name.0].time_rec =
                    time_rec + now.checked_duration_since(start).unwrap_or_default();
            }
            _ => {
                // For references, the type they point at isn't held by this object, but another heap value.
                // Therefore the true cost is just the reference itself.
                let typ = match x {
                    ValueMem::Ref(_) => "reference",
                    _ => x.get_aref().as_type_name(),
                };
                *self.top_info().allocs.entry(typ).or_insert(0) += 1;
            }
        }
    }
}

impl Heap {
    // We could expose profile on the Heap, but it's an implementation detail that it works here.
    pub(crate) fn write_profile(&self, filename: &Path) -> anyhow::Result<()> {
        let file = File::create(filename).with_context(|| {
            format!("When creating profile output file `{}`", filename.display())
        })?;
        self.write_profile_to(file).with_context(|| {
            format!(
                "When writing to profile output file `{}`",
                filename.display()
            )
        })
    }

    fn write_profile_to(&self, mut file: impl Write) -> io::Result<()> {
        let mut ids = FunctionIds::default();
        let root = ids.get_string("(root)".to_owned());
        let start = Instant::now();
        let mut info = Info {
            ids,
            info: Vec::new(),
            last_changed: start,
            call_stack: vec![(root, Duration::default(), start)],
        };
        info.ensure(root);
        self.for_each(|x| info.process(x));
        // Just has root left on it
        assert!(info.call_stack.len() == 1);

        // Add a totals column
        let total_id = info.ids.get_string("TOTALS".to_owned());
        info.ensure(total_id);
        let Info {
            mut info, mut ids, ..
        } = info;
        let totals = FuncInfo::merge(info.iter());
        let mut columns: Vec<(&'static str, usize)> =
            totals.allocs.iter().map(|(k, v)| (*k, *v)).collect();
        info[total_id.0] = totals;
        let mut info = info.iter().enumerate().collect::<Vec<_>>();

        columns.sort_by_key(|x| -(x.1 as isize));
        info.sort_by_key(|x| -(x.1.time.as_nanos() as i128));

        write!(
            file,
            "Function,Time(s),TimeRec(s),Calls,Callers,TopCaller,TopCallerCount,Allocs"
        )?;
        let trim_namespace = Regex::new("[a-z_]+::").unwrap();
        for x in &columns {
            // Given: starlark::values::list::ListGen<starlark::gc::value::Value>
            // We'd like: ListGen<Value>
            write!(file, ",{}", trim_namespace.replace_all(x.0, ""))?;
        }
        writeln!(file)?;
        let blank = ids.get_string("".to_owned());
        let un_ids = ids.invert();
        for (rowname, info) in info {
            let allocs = info.allocs.values().sum::<usize>();
            let callers = info
                .callers
                .iter()
                .max_by_key(|x| x.1)
                .unwrap_or((&blank, &0));
            write!(
                file,
                "\"{}\",{:.3},{:.3},{},{},\"{}\",{},{}",
                un_ids[rowname],
                info.time.as_secs_f64(),
                info.time_rec.as_secs_f64(),
                info.calls,
                info.callers.len(),
                un_ids[callers.0.0],
                callers.1,
                allocs
            )?;
            for x in &columns {
                write!(file, ",{}", info.allocs.get(x.0).unwrap_or(&0))?;
            }
            writeln!(file)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        environment::{Globals, Module},
        eval::Evaluator,
        syntax::{AstModule, Dialect},
        values::Value,
    };

    #[test]
    fn test_profiling() -> anyhow::Result<()> {
        // We don't test that the profile looks any particular way, but we do test it doesn't crash
        let ast = AstModule::parse(
            "foo.bzl",
            r#"
def f(x):
    return (x * 5) + 3
y = 8 * 9 + 2
f
"#
            .to_owned(),
            &Dialect::Extended,
        )?;
        let globals = Globals::standard();
        let module = Module::new();
        let mut eval = Evaluator::new(&module, &globals);
        eval.enable_profile();
        let f = eval.eval_module(ast)?;
        // first check module profiling works
        module.heap().write_profile_to(&mut Vec::new())?;

        // second check function profiling works
        let module = Module::new();
        let mut eval = Evaluator::new(&module, &globals);
        eval.enable_profile();
        eval.eval_function(f, &[Value::new_int(100)], &[])?;
        module.heap().write_profile_to(&mut Vec::new())?;

        // finally, check a user can add values into the heap before/after
        let module = Module::new();
        let mut eval = Evaluator::new(&module, &globals);
        module.heap().alloc("Thing that goes before");
        eval.enable_profile();
        eval.eval_function(f, &[Value::new_int(100)], &[])?;
        module.heap().alloc("Thing that goes after");
        module.heap().write_profile_to(&mut Vec::new())?;

        Ok(())
    }
}
