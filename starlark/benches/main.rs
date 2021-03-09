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
    eval::{eval_function, eval_module, EvaluationContext, NoLoadFileLoader},
    stdlib::extended_environment,
    syntax::{parse, Dialect},
};

fn benchmark_run(globals: &Globals, code: &str) {
    let env = Module::new();
    let mut ctx = EvaluationContext::new(&env, globals, &NoLoadFileLoader);
    let ast = parse("benchmark.sky", code.to_owned(), &Dialect::Standard).unwrap();
    eval_module(ast, &mut ctx).unwrap();
}

fn benchmark_pure_parsing(code: &str) {
    parse("benchmark.sky", code.to_owned(), &Dialect::Standard).unwrap();
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

const TIGHT_LOOP: &str = r#"
def bench():
    n = 10000
    x = 0
    for i in range(n + 1):
        x = x + i

    if(x != (n + 1) * n // 2):
        fail("Wrong answer!")

bench
"#;

pub fn criterion_general_benchmark(c: &mut Criterion, globals: &Globals) {
    c.bench_function("empty", |b| b.iter(|| benchmark_run(globals, EMPTY)));
    c.bench_function("bubble_sort", |b| {
        b.iter(|| benchmark_run(globals, BUBBLE_SORT))
    });
}

pub fn criterion_parsing_benchmark(c: &mut Criterion) {
    c.bench_function("parse_long_buble_sort", |b| {
        let long_code = &BUBBLE_SORT.repeat(100)[..];
        b.iter(|| benchmark_pure_parsing(long_code))
    });
}

pub fn criterion_eval_benchmark(c: &mut Criterion, globals: &Globals) {
    c.bench_function("run_tight_loop", |b| {
        let env = Module::new();
        let mut context = EvaluationContext::new(&env, globals, &NoLoadFileLoader);
        let ast = parse("benchmark.sky", TIGHT_LOOP.to_owned(), &Dialect::Standard).unwrap();
        let bench_function = eval_module(ast, &mut context).unwrap();
        b.iter(move || eval_function(bench_function, &[], &[], &mut context).unwrap())
    });
}

pub fn criterion_benchmark(c: &mut Criterion) {
    let g = extended_environment().build();
    criterion_general_benchmark(c, &g);
    criterion_parsing_benchmark(c);
    criterion_eval_benchmark(c, &g);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
