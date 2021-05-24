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

// This module contains stack-like data structures that tend to be super
// useful when writing an interpreter. As we refactor, various types
// and methods become used/unused on a fairly regular basis. Rather than
// trying to fight the dead-code checker, just give up for this module.
// Once everything is stable, it might be worth removing what we don't need.
#![allow(dead_code)]

use gazebo::prelude::*;
use std::{iter, mem};

#[derive(Default_)]
pub(crate) struct Stack<T> {
    // Invariant: If last is None, items must be empty
    last: Option<T>,
    items: Vec<T>,
}

impl<T> Stack<T> {
    pub fn push(&mut self, x: T) {
        let old = mem::replace(&mut self.last, Some(x));
        if let Some(old) = old {
            self.items.push(old)
        }
    }

    pub fn top(&mut self) -> &T {
        self.last.as_ref().unwrap()
    }

    pub fn top_mut(&mut self) -> &mut T {
        self.last.as_mut().unwrap()
    }

    pub fn pop(&mut self) -> T {
        mem::replace(&mut self.last, self.items.pop()).unwrap()
    }

    pub fn len(&self) -> usize {
        if self.last.is_none() {
            0
        } else {
            self.items.len() + 1
        }
    }

    pub fn truncate(&mut self, len: usize) {
        assert!(len <= self.len());
        if self.last.is_some() {
            // Keep the code simple - push me onto the Vec, truncate pop
            self.items.push(self.last.take().unwrap());
            self.items.truncate(len);
            self.last = self.items.pop();
        }
    }
}

#[derive(Default)]
pub(crate) struct Stack1<T> {
    top: T,
    rest: Vec<T>,
}

impl<T> Stack1<T> {
    pub fn push(&mut self, top: T) {
        self.rest.push(mem::replace(&mut self.top, top));
    }

    pub fn pop(&mut self) -> T {
        mem::replace(&mut self.top, self.rest.pop().unwrap())
    }

    pub fn top(&self) -> &T {
        &self.top
    }

    pub fn top_mut(&mut self) -> &mut T {
        &mut self.top
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.rest.iter_mut().chain(iter::once(&mut self.top))
    }

    pub fn len(&self) -> usize {
        self.rest.len() + 1
    }

    pub fn truncate(&mut self, len: usize) {
        assert!(len >= 1 && len <= self.len());
        let n = self.rest.len();
        if len == n + 1 {
            // nothing to do, didn't want truncation
        } else {
            self.rest.truncate(len + 1);
            self.top = self.rest.pop().unwrap()
        }
    }
}
