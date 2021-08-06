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
use crate::values::{Trace, Tracer, Value};
use anyhow::Context;
use std::{
    collections::{hash_map::Entry, HashMap},
    fs::File,
    io,
    io::Write,
    path::Path,
    slice,
    time::{Duration, Instant},
};

enum Frame<'v> {
    Push(Value<'v>),
    Pop,
}

#[derive(Trace)]
pub(crate) struct FlameProfile<'v> {
    #[allow(clippy::box_vec)] // Deliberately box to reduce memory usage when disabled
    frames: Option<Box<Vec<(Frame<'v>, Instant)>>>,
}

unsafe impl<'v> Trace<'v> for Frame<'v> {
    fn trace(&mut self, tracer: &Tracer<'v>) {
        match self {
            Frame::Push(x) => tracer.trace(x),
            Frame::Pop => {}
        }
    }
}

struct Stacks {
    name: String,
    time: Duration,
    children: HashMap<usize, Stacks>,
}

impl Stacks {
    fn blank(name: String) -> Self {
        Stacks {
            name,
            time: Duration::default(),
            children: HashMap::new(),
        }
    }

    fn new(frames: &[(Frame, Instant)]) -> Self {
        let mut res = Stacks::blank("root".to_owned());
        let mut last_time = frames.first().map_or_else(Instant::now, |x| x.1);
        res.add(&mut frames.iter(), &mut last_time);
        res
    }

    fn add(&mut self, frames: &mut slice::Iter<(Frame, Instant)>, last_time: &mut Instant) {
        while let Some((frame, time)) = frames.next() {
            self.time += time.duration_since(*last_time);
            *last_time = *time;
            match frame {
                Frame::Pop => return,
                Frame::Push(v) => match self.children.entry(v.ptr_value()) {
                    Entry::Occupied(mut e) => e.get_mut().add(frames, last_time),
                    Entry::Vacant(e) => e.insert(Stacks::blank(v.to_repr())).add(frames, last_time),
                },
            }
        }
    }

    fn render_with_buffer(&self, file: &mut impl Write, buffer: &mut String) -> io::Result<()> {
        // Reuse the buffer to accumulate the stack name
        let start_len = buffer.len();
        if !buffer.is_empty() {
            buffer.push(';')
        }
        buffer.push_str(&self.name);
        let count = self.time.as_millis();
        if count > 0 {
            writeln!(file, "{} {}", buffer, count)?;
        }
        for x in self.children.values() {
            x.render_with_buffer(file, buffer)?;
        }
        buffer.truncate(start_len);
        Ok(())
    }

    fn render(&self, mut file: impl Write) -> io::Result<()> {
        let mut buffer = String::new();
        self.render_with_buffer(&mut file, &mut buffer)
    }
}

impl<'v> FlameProfile<'v> {
    pub(crate) fn new() -> Self {
        Self { frames: None }
    }

    pub(crate) fn enable(&mut self) {
        self.frames = Some(box Vec::new());
    }

    pub fn record_call_enter(&mut self, function: Value<'v>) {
        if let Some(box x) = &mut self.frames {
            x.push((Frame::Push(function), Instant::now()))
        }
    }

    pub fn record_call_exit(&mut self) {
        if let Some(box x) = &mut self.frames {
            x.push((Frame::Pop, Instant::now()))
        }
    }

    // We could expose profile on the Heap, but it's an implementation detail that it works here.
    pub(crate) fn write(&self, filename: &Path) -> Option<anyhow::Result<()>> {
        self.frames
            .as_ref()
            .map(|box x| Self::write_enabled(x, filename))
    }

    fn write_enabled(frames: &[(Frame<'v>, Instant)], filename: &Path) -> anyhow::Result<()> {
        let file = File::create(filename).with_context(|| {
            format!("When creating profile output file `{}`", filename.display())
        })?;
        Self::write_profile_to(frames, file).with_context(|| {
            format!(
                "When writing to profile output file `{}`",
                filename.display()
            )
        })
    }

    fn write_profile_to(frames: &[(Frame<'v>, Instant)], file: impl Write) -> io::Result<()> {
        // Need to write out lines which look like:
        // root;calls1;calls2 1
        // All the numbers at the end must be whole numbers (we use milliseconds)
        Stacks::new(frames).render(file)
    }
}
