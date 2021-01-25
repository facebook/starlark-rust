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

use criterion::{criterion_group, criterion_main, Criterion};
use starlark::{
    environment::{Globals, Module},
    eval::eval_no_load,
    stdlib::extended_environment,
    syntax::Dialect,
};

fn benchmark_run(globals: &Globals, code: &str) {
    let mut env = Module::new("benchmark");
    eval_no_load("benchmark.sky", code, &Dialect::Standard, &mut env, globals).unwrap();
}

const EMPTY: &str = r#"
def bench():
    pass
bench()
"#;

const BUBBLE_SORT: &str = r#"
def bubble_sort(array):
    array = list(array)
    for i in range(len(array)):
        for j in range(len(array) - i - 1):
            if array[j] > array[j + 1]:
                array[j], array[j + 1] = array[j + 1], array[j]
    return array

def bench():
    if [2, 3, 4, 5, 6, 7, 9] != bubble_sort([9, 3, 5, 4, 7, 2, 6]):
        fail("Wrong answer!")
bench()
"#;

pub fn criterion_benchmark(c: &mut Criterion) {
    let g = extended_environment().build();
    c.bench_function("empty", |b| b.iter(|| benchmark_run(&g, EMPTY)));
    c.bench_function("bubble_sort", |b| b.iter(|| benchmark_run(&g, BUBBLE_SORT)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
