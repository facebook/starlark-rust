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

use crate as starlark;
use crate::values::{
    ComplexValue, Freezer, Heap, NoSimpleValue, SimpleValue, StarlarkValue, Trace, Value, ValueLike,
};
use anyhow::Context;
use derive_more::Display;
use gazebo::{any::AnyLifetime, prelude::*};
use std::{
    cell::RefCell,
    collections::{hash_map::Entry, HashMap},
    fs::File,
    io::Write,
    path::Path,
    rc::Rc,
    time::{Duration, Instant},
};

#[derive(Copy, Clone, Dupe, Debug)]
pub(crate) enum HeapProfileFormat {
    Summary,
    FlameGraph,
}

pub(crate) struct HeapProfile {
    enabled: bool,
}

#[derive(AnyLifetime, Trace, Debug, Display)]
#[display(fmt = "CallEnter")]
struct CallEnter<'v> {
    function: Value<'v>,
    time: Instant,
    memory: usize,
}

impl<'v> ComplexValue<'v> for CallEnter<'v> {
    type Frozen = NoSimpleValue;
    fn freeze(self, _freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
        unreachable!("Should never end up freezing a CallEnter")
    }
}

impl<'v> StarlarkValue<'v> for CallEnter<'v> {
    starlark_type!("call_enter");
}

#[derive(AnyLifetime, Debug, Display)]
#[display(fmt = "CallExit")]
struct CallExit {
    time: Instant,
    memory: usize,
}

impl SimpleValue for CallExit {}

impl<'v> StarlarkValue<'v> for CallExit {
    starlark_type!("call_exit");
}

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

impl HeapProfile {
    pub(crate) fn new() -> Self {
        Self { enabled: false }
    }

    pub(crate) fn enable(&mut self) {
        self.enabled = true;
    }

    pub(crate) fn record_call_enter<'v>(&self, function: Value<'v>, heap: &'v Heap) {
        if self.enabled {
            heap.alloc_complex(CallEnter {
                function,
                time: Instant::now(),
                memory: heap.allocated_bytes_inline(),
            });
        }
    }

    pub(crate) fn record_call_exit<'v>(&self, heap: &'v Heap) {
        if self.enabled {
            heap.alloc_simple(CallExit {
                time: Instant::now(),
                memory: heap.allocated_bytes_inline(),
            });
        }
    }

    // We could expose profile on the Heap, but it's an implementation detail that it works here.
    pub(crate) fn write(
        &self,
        filename: &Path,
        heap: &Heap,
        format: HeapProfileFormat,
    ) -> Option<anyhow::Result<()>> {
        if !self.enabled {
            None
        } else {
            Some(Self::write_enabled(filename, heap, format))
        }
    }

    pub(crate) fn write_enabled(
        filename: &Path,
        heap: &Heap,
        format: HeapProfileFormat,
    ) -> anyhow::Result<()> {
        let file = File::create(filename).with_context(|| {
            format!("When creating profile output file `{}`", filename.display())
        })?;

        match format {
            HeapProfileFormat::Summary => Self::write_summarized_heap_profile_to(file, heap),
            HeapProfileFormat::FlameGraph => Self::write_flame_heap_profile_to(file, heap),
        }
        .with_context(|| {
            format!(
                "When writing to profile output file `{}`",
                filename.display()
            )
        })
    }

    fn write_flame_heap_profile_to(mut file: impl Write, heap: &Heap) -> anyhow::Result<()> {
        let mut collector = flame::StackCollector::new();
        heap.for_each_ordered(|x| collector.process(x));
        collector.write_to(&mut file)?;
        Ok(())
    }

    fn write_summarized_heap_profile_to(mut file: impl Write, heap: &Heap) -> anyhow::Result<()> {
        use summary::{FuncInfo, Info};

        let mut ids = FunctionIds::default();
        let root = ids.get_string("(root)".to_owned());
        let start = Instant::now();
        let mut info = Info {
            ids,
            info: Vec::new(),
            last_changed: (start, 0),
            call_stack: vec![(root, Duration::default(), start)],
        };
        info.ensure(root);
        heap.for_each_ordered(|x| info.process(x));
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
            "Function,Time(s),TimeRec(s),Calls,Callers,TopCaller,TopCallerCount,Bytes,Allocs"
        )?;
        for x in &columns {
            write!(file, ",\"{}\"", &x.0)?;
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
                "\"{}\",{:.3},{:.3},{},{},\"{}\",{},{},{}",
                un_ids[rowname],
                info.time.as_secs_f64(),
                info.time_rec.as_secs_f64(),
                info.calls,
                info.callers.len(),
                un_ids[callers.0.0],
                callers.1,
                info.memory,
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

mod summary {
    use super::*;

    /// Information relating to a function.
    #[derive(Default, Debug, Clone)]
    pub(super) struct FuncInfo {
        /// Number of times this function was called
        pub calls: usize,
        /// Who called this function (and how many times each)
        pub callers: HashMap<FunctionId, usize>,
        /// Time spent directly in this function
        pub time: Duration,
        /// Inline memory used directly in this function
        pub memory: usize,
        /// Time spent directly in this function and recursive functions.
        pub time_rec: Duration,
        /// Allocations made by this function
        pub allocs: HashMap<&'static str, usize>,
    }

    impl FuncInfo {
        pub fn merge<'a>(xs: impl Iterator<Item = &'a Self>) -> Self {
            let mut result = Self::default();
            for x in xs {
                result.calls += x.calls;
                result.time += x.time;
                result.memory += x.memory;
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
    pub(super) struct Info {
        pub ids: FunctionIds,

        /// Information about all functions
        pub info: Vec<FuncInfo>,
        /// When the top of the stack last changed
        pub last_changed: (Instant, usize),
        /// Each entry is (Function, time_rec when I started, time I started)
        /// The time_rec is recorded so that recursion doesn't screw up time_rec
        pub call_stack: Vec<(FunctionId, Duration, Instant)>,
    }

    impl Info {
        pub fn ensure(&mut self, x: FunctionId) {
            if self.info.len() <= x.0 {
                self.info.resize(x.0 + 1, FuncInfo::default());
            }
        }

        pub fn top_id(&self) -> FunctionId {
            self.call_stack.last().unwrap().0
        }

        pub fn top_info(&mut self) -> &mut FuncInfo {
            let top = self.top_id();
            &mut self.info[top.0]
        }

        /// Called before you change the top of the stack
        fn change(&mut self, time: Instant, memory: usize) {
            let (old_time, old_memory) = self.last_changed;
            let ti = self.top_info();
            ti.time += time.checked_duration_since(old_time).unwrap_or_default();
            ti.memory += memory - old_memory;
            self.last_changed = (time, memory);
        }

        /// Process each ValueMem in their chronological order
        pub fn process<'v>(&mut self, x: Value<'v>) {
            if let Some(CallEnter {
                function,
                time,
                memory,
            }) = x.downcast_ref()
            {
                let id = self.ids.get_value(*function);
                self.ensure(id);
                self.change(*time, *memory);

                let top = self.top_id();
                let mut me = &mut self.info[id.0];
                me.calls += 1;
                *me.callers.entry(top).or_insert(0) += 1;
                self.call_stack.push((id, me.time_rec, *time));
            } else if let Some(CallExit { time, memory }) = x.downcast_ref() {
                self.change(*time, *memory);
                let (name, time_rec, start) = self.call_stack.pop().unwrap();
                self.info[name.0].time_rec =
                    time_rec + time.checked_duration_since(start).unwrap_or_default();
            } else {
                let typ = x.get_ref().get_type();
                *self.top_info().allocs.entry(typ).or_insert(0) += 1;
            }
        }
    }
}

mod flame {
    use super::*;

    /// Allocations made in a given stack frame for a given type.
    #[derive(Default)]
    struct StackFrameAllocations {
        bytes: usize,
        count: usize,
    }

    /// A stack frame, its caller and the functions it called, and the allocations it made itself.
    struct StackFrameData {
        caller: Option<StackFrame>,
        callees: HashMap<FunctionId, StackFrame>,
        allocs: HashMap<&'static str, StackFrameAllocations>,
    }

    #[derive(Clone, Dupe)]
    struct StackFrame(Rc<RefCell<StackFrameData>>);

    impl StackFrame {
        fn new(caller: impl Into<Option<StackFrame>>) -> Self {
            Self(Rc::new(RefCell::new(StackFrameData {
                caller: caller.into(),
                callees: Default::default(),
                allocs: Default::default(),
            })))
        }

        /// Enter a new stack frame.
        fn push(&self, function: FunctionId) -> Self {
            let mut this = self.0.borrow_mut();

            let callee = this
                .callees
                .entry(function)
                .or_insert_with(|| Self::new(self.dupe()));

            callee.dupe()
        }

        /// Exit the last stack frame.
        fn pop(&self) -> Option<Self> {
            let this = self.0.borrow();
            this.caller.as_ref().duped()
        }

        /// Write this stack frame's data to a file in a format flamegraph.pl understands
        /// (each line is: `func1:func2:func3 BYTES`).
        fn write<'a>(
            &self,
            file: &mut impl Write,
            stack: &'_ mut Vec<&'a str>,
            ids: &[&'a str],
        ) -> anyhow::Result<()> {
            let this = self.0.borrow();

            for (k, v) in this.allocs.iter() {
                for e in stack.iter().chain(std::iter::once(k)).intersperse(&";") {
                    write!(file, "{}", e)?;
                }
                writeln!(file, " {}", v.bytes)?;
            }

            for (id, frame) in this.callees.iter() {
                stack.push(ids[id.0]);
                frame.write(file, stack, ids)?;
                stack.pop();
            }

            Ok(())
        }
    }

    /// An accumulator for stack frames that lets us visit the heap.
    pub struct StackCollector {
        ids: FunctionIds,
        current: Option<StackFrame>,
    }

    impl StackCollector {
        pub fn new() -> Self {
            Self {
                ids: FunctionIds::default(),
                current: Some(StackFrame::new(None)),
            }
        }

        /// Visit a value from the heap.
        pub fn process<'v>(&mut self, x: Value<'v>) {
            let frame = match self.current.as_ref() {
                Some(frame) => frame,
                None => return,
            };

            if let Some(CallEnter { function, .. }) = x.downcast_ref() {
                // New frame, enter it.
                let id = self.ids.get_value(*function);
                self.current = Some(frame.push(id));
            } else if let Some(CallExit { .. }) = x.downcast_ref() {
                // End of frame, exit!
                self.current = frame.pop();
            } else {
                // Value allocated in this frame, record it!
                let typ = x.get_ref().get_type();
                let mut frame = frame.0.borrow_mut();
                let mut entry = frame.allocs.entry(typ).or_default();
                entry.bytes += x.get_ref().total_memory();
                entry.count += 1;
            }
        }

        /// Write this our recursively to a file.
        pub fn write_to(&self, file: &mut impl Write) -> anyhow::Result<()> {
            let current = self.current.as_ref().context("Popped the root frame")?;
            current
                .write(file, &mut vec![], &self.ids.invert())
                .context("Writing failed")?;
            Ok(())
        }
    }

    /// This needs a customized Drop since we have self-referential RCs. If we drop all the
    /// caller fields then that lets the struct get freed.
    impl Drop for StackCollector {
        fn drop(&mut self) {
            fn clear_caller(f: &StackFrame) {
                let mut this = f.0.borrow_mut();
                this.caller = None;

                for callee in this.callees.values() {
                    clear_caller(callee);
                }
            }

            if let Some(frame) = self.current.as_ref() {
                clear_caller(frame)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
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
        eval.enable_heap_profile();
        let f = eval.eval_module(ast)?;
        // first check module profiling works
        HeapProfile::write_summarized_heap_profile_to(&mut Vec::new(), module.heap())?;
        HeapProfile::write_flame_heap_profile_to(&mut Vec::new(), module.heap())?;

        // second check function profiling works
        let module = Module::new();
        let mut eval = Evaluator::new(&module, &globals);
        eval.enable_heap_profile();
        eval.eval_function(f, &[Value::new_int(100)], &[])?;
        HeapProfile::write_summarized_heap_profile_to(&mut Vec::new(), module.heap())?;
        HeapProfile::write_flame_heap_profile_to(&mut Vec::new(), module.heap())?;

        // finally, check a user can add values into the heap before/after
        let module = Module::new();
        let mut eval = Evaluator::new(&module, &globals);
        module.heap().alloc("Thing that goes before");
        eval.enable_heap_profile();
        eval.eval_function(f, &[Value::new_int(100)], &[])?;
        module.heap().alloc("Thing that goes after");
        HeapProfile::write_summarized_heap_profile_to(&mut Vec::new(), module.heap())?;
        HeapProfile::write_flame_heap_profile_to(&mut Vec::new(), module.heap())?;

        Ok(())
    }
}
