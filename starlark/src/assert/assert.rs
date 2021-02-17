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

//! Utilities to test Starlark code execution.
//! All run using the [extended_environment].
use crate::{
    self as starlark,
    collections::SmallMap,
    environment::{FrozenModule, Globals, GlobalsBuilder, Module},
    errors::{eprint_error, Diagnostic},
    eval,
    stdlib::{add_typing, extended_environment},
    syntax::Dialect,
    values::{
        none::{NoneType, NONE},
        structs::Struct,
        OwnedFrozenValue, Value,
    },
};
use anyhow::anyhow;
use gazebo::prelude::*;
use once_cell::sync::Lazy;
use std::collections::HashMap;

fn mk_environment() -> GlobalsBuilder {
    extended_environment().with(test_methods).with(add_typing)
}

static GLOBALS: Lazy<Globals> = Lazy::new(|| mk_environment().build());

static ASSERT_STAR: Lazy<FrozenModule> = Lazy::new(|| {
    let g = GlobalsBuilder::new()
        .with_struct("assert", assert_star)
        .build();
    let m = Module::new("assert.star");
    m.frozen_heap().add_reference(g.heap());
    let assert = g.get("assert").unwrap();
    m.set("assert", assert);
    m.set("freeze", assert.get_attr("freeze", m.heap()).unwrap());
    m.freeze()
});

fn assert_equals<'v>(a: Value<'v>, b: Value<'v>) -> anyhow::Result<NoneType> {
    if !a.equals(b)? {
        Err(anyhow!("assert_eq: expected {}, got {}", a, b))
    } else {
        Ok(NONE)
    }
}

/// Definitions to support assert.star as used by the Go test suite
#[starlark_module]
fn assert_star(builder: &mut GlobalsBuilder) {
    fn eq(a: Value, b: Value) -> NoneType {
        assert_equals(a, b)
    }

    fn ne(a: Value, b: Value) -> NoneType {
        if a.equals(b)? {
            Err(anyhow!(
                "assert.ne: expected {} and {} different, but the same",
                a,
                b
            ))
        } else {
            Ok(NONE)
        }
    }

    fn contains(xs: Value, x: Value) -> NoneType {
        if !xs.is_in(x)? {
            Err(anyhow!("assert.contains: expected {} to be in {}", x, xs))
        } else {
            Ok(NONE)
        }
    }

    fn r#true(x: Value) -> NoneType {
        assert_equals(Value::new_bool(x.to_bool()), Value::new_bool(true))
    }

    // We don't allow this at runtime - just to be compatible with the Go Starlark test suite
    fn freeze(x: Value) -> Value<'v> {
        Ok(x)
    }

    fn fails(f: Value, _msg: &str) -> NoneType {
        let invoke = f.new_invoker(heap)?;
        match invoke.invoke(f, None, ctx) {
            Err(_e) => Ok(NONE), // We don't actually check the message
            Ok(_) => Err(anyhow!("assert.fails: didn't fail")),
        }
    }
}

#[starlark_module]
fn test_methods(builder: &mut GlobalsBuilder) {
    // Used by one of the test methods in Go
    const fibonacci: Vec<i32> = vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89];

    // Approximate version of a method used by the Go test suite
    fn hasfields() -> Struct<'v> {
        Ok(Struct::new(SmallMap::new()))
    }

    // Approximate version of a method used by the Go test suite
    fn set(xs: Value) -> Value<'v> {
        Ok(xs)
    }

    fn assert_eq(a: Value, b: Value) -> NoneType {
        assert_equals(a, b)
    }

    fn print(x: Value) -> NoneType {
        println!("{}", x);
        Ok(NONE)
    }
}

#[derive(Clone)]
pub struct Assert {
    dialect: Dialect,
    modules: HashMap<String, FrozenModule>,
    globals: Globals,
}

impl Assert {
    pub fn new() -> Self {
        Self {
            dialect: Dialect {
                enable_types: true,
                ..Dialect::Extended
            },
            modules: hashmap!["assert.star".to_owned() => Lazy::force(&ASSERT_STAR).dupe()],
            globals: Lazy::force(&GLOBALS).dupe(),
        }
    }

    fn execute<'a>(&self, path: &str, program: &str, env: &'a Module) -> anyhow::Result<Value<'a>> {
        let mut modules = HashMap::with_capacity(self.modules.len());
        for (k, v) in &self.modules {
            modules.insert(k.clone(), v);
        }
        eval::eval_with_modules(
            path,
            program.to_owned(),
            &self.dialect,
            env,
            &self.globals,
            &modules,
        )
    }

    fn execute_fail<'a>(&self, func: &str, program: &str, env: &'a Module) -> anyhow::Error {
        match self.execute("test.bzl", program, env) {
            Ok(v) => panic!(
                "starlark::assert::{}, didn't fail!\nCode:\n{}\nResult:\n{}\n",
                func, program, v
            ),
            Err(e) => e,
        }
    }

    fn execute_unwrap<'a>(
        &self,
        func: &str,
        path: &str,
        program: &str,
        env: &'a Module,
    ) -> Value<'a> {
        match self.execute(path, program, env) {
            Ok(v) => v,
            Err(err) => {
                eprint_error(&err);
                panic!(
                    "starlark::assert::{}, failed to execute!\nCode:\n{}\nGot error: {}",
                    func, program, err
                );
            }
        }
    }

    fn execute_unwrap_true<'a>(&self, func: &str, program: &str, env: &'a Module) {
        let v = self.execute_unwrap(func, "test.bzl", program, env);
        match v.unpack_bool() {
            Some(true) => {}
            Some(false) => panic!("starlark::assert::{}, got false!\nCode:\n{}", func, program),
            None => panic!(
                "starlark::assert::{}, not a bool!\nCode:\n{}\nResult\n{}",
                func, program, v
            ),
        }
    }

    pub fn dialect(&mut self, x: &Dialect) {
        self.dialect = x.clone();
    }

    pub fn dialect_set(&mut self, f: impl FnOnce(&mut Dialect)) {
        f(&mut self.dialect)
    }

    pub fn module_add(&mut self, name: &str, module: FrozenModule) {
        self.modules.insert(name.to_owned(), module);
    }

    pub fn module(&mut self, name: &str, program: &str) {
        let module = Module::new(name);
        self.execute_unwrap("module", &format!("{}.bzl", name), program, &module);
        self.module_add(name, module.freeze());
    }

    pub fn get_globals(&self) -> Globals {
        self.globals.dupe()
    }

    pub fn globals(&mut self, x: Globals) {
        self.globals = x;
    }

    pub fn globals_add(&mut self, f: impl FnOnce(&mut GlobalsBuilder)) {
        self.globals(mk_environment().with(f).build())
    }

    fn fails_with_name(&self, func: &str, program: &str, msgs: &[&str]) -> anyhow::Error {
        let module_env = Module::new(func);
        let original = self.execute_fail(func, program, &module_env);
        // We really want to check the error message, but if in our doc tests we do:
        // fail("bad") # error: magic
        // Then when we print the source code, magic is contained in the error message.
        // Therefore, find the internals.
        let inner = original
            .downcast_ref::<Diagnostic>()
            .map_or(&original, |d| &d.message);
        let err_msg = format!("{:#}", inner);
        for msg in msgs {
            if !err_msg.contains(msg) {
                eprint_error(&original);
                panic!(
                    "starlark::assert::{}, failed with the wrong message!\nCode:\n{}\nError:\n{}\nMissing:\n{}\nExpected:\n{:?}",
                    func, program, inner, msg, msgs
                )
            }
        }
        original
    }

    pub fn fail(&self, program: &str, msg: &str) -> anyhow::Error {
        self.fails_with_name("fail", program, &[msg])
    }

    pub fn fails(&self, program: &str, msgs: &[&str]) -> anyhow::Error {
        self.fails_with_name("fails", program, msgs)
    }

    pub fn pass(&self, program: &str) -> OwnedFrozenValue {
        let env = Module::new("pass");
        let res = self.execute_unwrap("pass", "test.bzl", program, &env);
        env.set("_", res);
        env.freeze().get("_").unwrap()
    }

    pub fn is_true(&self, program: &str) {
        let env = Module::new("assert");
        self.execute_unwrap_true("is_true", program, &env);
    }

    pub fn all_true(&self, program: &str) {
        for s in program.lines() {
            if s == "" {
                continue;
            }
            let env = Module::new("assert");
            self.execute_unwrap_true("all_true", s, &env);
        }
    }

    pub fn eq(&self, lhs: &str, rhs: &str) {
        let lhs_m = Module::new("lhs");
        let rhs_m = Module::new("rhs");
        let lhs_v = self.execute_unwrap("eq", "lhs.bzl", lhs, &lhs_m);
        let rhs_v = self.execute_unwrap("eq", "rhs.bzl", rhs, &rhs_m);
        if lhs_v != rhs_v {
            panic!(
                "starlark::assert::eq, values differ!\nCode 1:\n{}\nCode 2:\n{}\nValue 1:\n{}\nValue 2\n{}",
                lhs, rhs, lhs_v, rhs_v
            );
        }
    }
}

/// Two programs that must evaluate to the same (non-error) result.
///
/// ```
/// starlark::assert::eq("1 + 1", "2");
/// ```
pub fn eq(lhs: &str, rhs: &str) {
    Assert::new().eq(lhs, rhs)
}

/// A program that must fail with an error message that contains a specific
/// string. Remember that the purpose of `fail` is to ensure you get
/// the right error, not to fully specify the error - usually only one or
/// two words will be sufficient to ensure that.
///
/// ```
/// starlark::assert::fail("fail('hello')", "ello");
/// ```
pub fn fail(program: &str, msg: &str) {
    Assert::new().fail(program, msg);
}

/// A program that must fail with an error message that contains a specific
/// set of strings. Remember that the purpose of `fail` is to ensure you get
/// the right error, not to fully specify the error - usually only one or
/// two words will be sufficient to ensure that. The words do not have to be
/// in order.
///
/// ```
/// starlark::assert::fails("fail('hello')", &["fail", "ello"]);
/// ```
pub fn fails(program: &str, msgs: &[&str]) {
    Assert::new().fails(program, msgs);
}

/// A program that must be true.
///
/// ```
/// starlark::assert::is_true(r#"
/// x = 1 + 1
/// x == 2
/// "#);
/// ```
pub fn is_true(program: &str) {
    Assert::new().is_true(program)
}

/// Many lines, each of which must be individually true (or blank).
///
/// ```
/// starlark::assert::all_true(r#"
/// 1 == 1
///
/// 2 == 1 + 1
/// "#);
/// ```
pub fn all_true(expressions: &str) {
    Assert::new().all_true(expressions)
}

/// A program that must be true, which has access to an external module.
///
/// ```
/// starlark::assert::is_true_with("x", "y = 2", r#"
/// load("x", "y")
/// y == 1 + 1
/// "#);
/// ```
pub fn is_true_with(module_name: &str, module_contents: &str, program: &str) {
    let mut a = Assert::new();
    a.module(module_name, module_contents);
    a.is_true(program)
}

/// A program that must fail with an error message that contains a specific
/// string, which has access to an external module.
///
/// ```
/// starlark::assert::fail_with("x", "def f():\n    fail('hello')", r#"
/// load("x", "f")
/// f()
/// "#, "hell");
/// ```
pub fn fail_with(module_name: &str, module_contents: &str, program: &str, msg: &str) {
    let mut a = Assert::new();
    a.module(module_name, module_contents);
    a.fail(program, msg);
}

/// A program that must execute successfully without an exception. Often uses
/// assert_eq. Returns the resulting value.
///
/// ```
/// starlark::assert::pass("assert_eq(1, 1)");
/// ```
pub fn pass(program: &str) -> OwnedFrozenValue {
    Assert::new().pass(program)
}
