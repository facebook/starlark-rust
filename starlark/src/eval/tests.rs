/*
 * Copyright 2018 The Starlark in Rust Authors.
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
    self as starlark,
    assert::{self, Assert},
    environment::{Globals, GlobalsBuilder, Module},
    errors::eprint_error,
    eval::Evaluator,
    syntax::{AstModule, Dialect},
    values::{any::StarlarkAny, none::NoneType, Heap, Value},
};
use gazebo::any::AnyLifetime;
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::{
    collections::HashMap,
    mem,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex,
    },
};

#[test]
fn arithmetic_test() {
    assert::is_true("(1 + 2 == 3)");
    assert::is_true("(1 * 2 == 2)");
    assert::is_true("(-1 * 2 == -2)");
    assert::is_true("(5 // 2 == 2)");
    assert::is_true("(5 % 2 == 1)");
}

#[test]
fn bitwise_test() {
    assert::all_true(
        r#"
3 & 6 == 2
3 & 6 == 2
-3 & 6 == 4
3 | 6 == 7
3 | -6 == -5
3 ^ 6 == 5
-3 ^ 6 == -5
-3 ^ -6 == 7
1 << 2 == 4
-1 << 2 == -4
1 >> 0 == 1
111 >> 2 == 27
~31 == -32
~-31 == 30
"#,
    );

    // For now, we report negative shift amounts as integer overflow
    assert::fail("1 << -13", "overflow");
    assert::fail("1 >> -13", "overflow");
}

#[test]
fn alias_test() {
    assert::is_true(
        r#"
a = [1, 2, 3]
b = a
a[2] = 0
a == [1, 2, 0] and b == [1, 2, 0]
"#,
    )
}

#[test]
fn recursive_list() {
    assert::is_true(
        r#"
cyclic = [1, 2, 3]
cyclic[1] = cyclic
len(cyclic) == 3 and len(cyclic[1]) == 3
"#,
    )
}

#[test]
fn funcall_test() {
    fn f(x: &str) -> String {
        format!(
            "
def f1():
  return 1

def f2(a): return a

def f3(a, b, c):
   return a + b + c

def f4(a, *args):
    r = a
    for i in args:
      r += i
    return r

def f5(a, **kwargs): return kwargs
def f6(*args): return args

def rec1(): rec1()

def rec2(): rec3()
def rec3(): rec4()
def rec4(): rec5()
def rec5(): rec6()
def rec6(): rec2()
{}",
            x
        )
    }
    assert::is_true(&f("(f1() == 1)"));
    assert::is_true(&f("(f2(2) == 2)"));
    assert::is_true(&f("(f3(1, 2, 3) == 6)"));
    assert::is_true(&f("(f4(1, 2, 3) == 6)"));
    assert::is_true(&f("(f5(2) == {})"));
    assert::is_true(&f("(f5(a=2) == {})"));
    assert::is_true(&f("(f5(1, b=2) == {'b': 2})"));
    assert::is_true(&f("(f6(1, 2, 3) == (1, 2, 3))"));
    // Recursion limit
    assert::fail(&f("rec1()"), "recursion");
    assert::fail(&f("rec2()"), "recursion");
    // multiple argument with the same name should not be allowed
    assert::fail("def f(a, a=2): pass", "duplicated parameter");
    // Invalid order of parameter
    assert::is_true("def f(a, *args, b): return b\nf(1, b=True)");
    assert::is_true("def f(a, *args, b=True): return b\nf(1)");
    assert::is_true("NAME=True\ndef f(*args, pkg=NAME, **kwargs): return pkg\nf()");
    assert::is_true("def f(*args, pkg=False, **kwargs): return pkg\nf(pkg=True)");
    assert::is_true("def f(a, b=1, *args, c=False): return c\nf(a=1,c=True)");
    assert::fail("def f(a, **kwargs, b=1): pass", "Default parameter after");
    assert::fail(
        "def f(a, b=1, **kwargs, c=1): pass",
        "Default parameter after",
    );
    assert::fail("def f(a, **kwargs, *args): pass", "parameter after another");
}

#[test]
fn funcall_extra_args_def() {
    fn f(x: &str) -> String {
        format!(
            "
def f3(a, b, c):
   return a + b + c
{}",
            x
        )
    }
    assert::fail(&f("f3(1,2,3,4)"), "extra positional");
    assert::fail(&f("f3(1,2)"), "Missing parameter");
    assert::fail(&f("f3(a=1, b=2)"), "Missing parameter");
    assert::fail(&f("f3(a=1, b=2, c=3, d=4)"), "extra named");
}

#[test]
fn test_repeated_parameters() {
    // Starlark requires both these types of errors are _static_ errors
    assert::fail("def f(x,x): pass", "duplicated parameter");
    assert::fail("def f(): pass\ndef g(): f(x=1,x=1)", "repeated named");
}

#[test]
fn test_context_captured() {
    let mut a = Assert::new();
    a.module("f.bzl", "x = 17\ndef f(): return x");
    // Import `f` but do not import `x`
    a.is_true("load('f.bzl', 'f')\nf() == 17");
}

#[test]
fn test_bad_application() {
    assert::fail("['1'](2)", "not supported");
    assert::fail("\"test\"(2)", "not supported");
    assert::fail("(1 == 1)(2)", "not supported");
}

#[test]
fn test_extra_args_native() {
    // Check that extra native arguments fail.
    // In this module to use String functions as a test suite.
    assert::is_true(r#"("bonbon".find("on") == 1)"#);
    // Should fail because find declares #needle, so hide the parameter
    assert::fail(
        r#"("bonbon".find(needle = "on") == 1)"#,
        "Missing parameter",
    );
    assert::fail(r#""bonbon".find("on", 2, 3, 4)"#, "extra positional");
    assert::fail(r#""bonbon".find("on", needless="on")"#, "extra named");
    assert::fail(r#""bonbon".find()"#, "Missing parameter");
}

#[test]
fn test_bad_break() {
    assert::fails("break", &["break", "outside of", "loop"]);
    assert::fails(
        "def foo(x):\n  if 1:\n    break",
        &["break", "outside of", "loop"],
    );
    assert::fails(
        "def foo(x):\n  if 1:\n    continue",
        &["continue", "outside of", "loop"],
    );
    assert::fail(
        "
def foo(x):
    for y in x:
        def bar(y):
            continue",
        "outside of",
    );
    assert::fail("return 1", "outside of a `def`");
    assert::fail("for x in []:\n  return 1", "outside of a `def`");
}

#[test]
fn test_tabs_fail() {
    let mut a = Assert::new();
    a.dialect_set(|d| d.enable_tabs = false);
    a.fail("def f():\n\tpass", "Parse error");
    a.fail("def f():\n x\t=3", "Parse error");
}

#[test]
fn test_tabs_pass() {
    assert::pass("def f():\n '\t'");
    let mut a = Assert::new();
    a.dialect(&Dialect::Standard);
    a.pass("def f():\n\tpass");
    a.pass("def f():\n x\t=3");
}

#[test]
fn test_lambda() {
    assert::is_true("(lambda x: x)(1) == 1");
    assert::is_true("(lambda x: (x == 1))(1)");
    assert::is_true(
        "
xs = [lambda x: x + y for y in [1,2,3]]
ys = [lambda x: x + y for y in [4,5,6]]
[xs[1](0),ys[1](0)] == [3,6]",
    );
}

#[test]
fn test_frozen_lambda() {
    let mut a = Assert::new();
    a.module(
        "lam",
        r#"
def my_func(a):
    return lambda b: a + b
add18 = my_func(18)
# This test used to fail if a GC happend, so add one
garbage_collect()
"#,
    );
    a.pass(
        r#"
load("lam", "add18")
assert_eq(add18(24), 42)
"#,
    );
}

#[test]
fn test_eval_function() {
    let fun = assert::pass(
        r#"
def fun(a, y, x = 1):
    return str((a, y, x))
fun
"#,
    );
    let env = Module::new();
    let globals = Globals::default();
    let mut eval = Evaluator::new(&env, &globals);
    let hello = env.heap().alloc("hello");
    let v = eval
        .eval_function(fun.value(), &[Value::new_int(8)], &[("y", hello)])
        .unwrap();
    assert_eq!(v.unpack_str(), Some("(8, \"hello\", 1)"))
}

#[test]
fn test_nested_def() {
    assert::is_true(
        "
def foo(x):
    def bar(y):
        return x+y
    return bar(x)
foo(8) == 16",
    );
    assert::is_true(
        "
def squarer():
    x = [0]
    def f():
        x[0] += 1
        return x[0]*x[0]
    return f
sq = squarer()
[sq(), sq(), sq(), sq()] == [1,4,9,16]",
    );
    assert::is_true(
        "
def f(x):
    def g(y):
        return lambda z: x + y + z
    return g
f(1)(2)(3) == 6",
    );
}

#[test]
fn test_garbage_collect() {
    assert::pass(
        r#"
x = (100, [{"test": None}], True)
y = str(x)
garbage_collect()
assert_eq(y, str(x))
    "#,
    );
}

#[test]
fn test_def_freeze() {
    let mut a = Assert::new();
    a.module(
        "f.bzl",
        r#"
def f(g):
    g(1)"#,
    );
    a.is_true(
        r#"
load('f.bzl', 'f')
x = []
def g(y):
    x.append(y)
f(g)
x == [1]"#,
    );
}

#[test]
fn test_comprehension() {
    // comprehensions should work whether they are at the root, or under a def
    // but these are actually quite different locations semantically, so test both
    fn check_comp(lines: &[&str]) {
        assert::is_true(&lines.join("\n"));
        let (last, init) = lines.split_last().unwrap();
        assert::is_true(&format!(
            "def f():\n  {}\n  return {}\nf()",
            init.join("\n  "),
            last
        ));
    }

    // From the Starlark spec
    check_comp(&["[x*x for x in [0,1,2,3,4]] == [0, 1, 4, 9, 16]"]);
    check_comp(&["[x*x for x in [0,1,2,3,4] if x%2 == 0] == [0, 4, 16]"]);
    check_comp(&[
        "[(x, y) for x in [0,1,2,3,4] if x%2 == 0 for y in [0,1,2,3,4] if y > x] == [(0, 1), (0, 2), (0, 3), (0, 4), (2, 3), (2, 4)]",
    ]);
    check_comp(&[r#"[x*y+z for (x, y), z in [((2, 3), 5), (("o", 2), "!")]] == [11, 'oo!']"#]);
    assert::fail("[x*x for x in 1, 2, 3]", "Parse error");
    check_comp(&["x = 1", "_ = [x for x in [2]]", "x == 1"]);

    // Dict comprehensions
    check_comp(&["{x: 1 for x in [0,1,2]} == {0: 1, 1: 1, 2: 1}"]);

    // Nested comprehensions
    check_comp(&["[[y for y in x] for x in [[1],[2,3]]] == [[1],[2,3]]"]);
    check_comp(&["[[x for x in x] for x in [[1],[2,3]]] == [[1],[2,3]]"]);
    check_comp(&["[x for x in [[1],[2,3]] for x in x if x >= 2] == [2,3]"]);
    check_comp(&[
        "items = {8: [1,2], 9: [3,4,6]}",
        "[[x for x in items[x] if x%2==0] for x in items] == [[2],[4,6]]",
    ]);

    // Sequential comprehensions
    check_comp(&[
        "x = [x*x for x in [0,1,2,3,4]]",
        "[x*x for x in x] == [0, 1, 16, 81, 256]",
    ]);

    // If only comprehensions are parse errors
    assert::fail("[1 if 0 == 0] == [0]", "Parse error");
}

#[test]
fn test_top_level_statements() {
    assert::pass(
        r#"
j = 0
for i in range(10):
    if i % 2 == 0:
        j += i
assert_eq(j, 20)
"#,
    );
}

#[test]
fn test_parameter_defaults() {
    assert::is_true(
        "
def f(x=[x for x in [1]]):
    return x
f() == [1]",
    );
    assert::is_true(
        "
y = 7
def f(x=y):
    y = 1
    return x
f() == 7",
    );
    assert::is_true(
        "
def f(x, xs = []):
    xs.append(x)
    return xs
pre = str(f(8, [6,7]))
f(1)
post = str(f(2))
pre == '[6, 7, 8]' and post == '[1, 2]'",
    );
}

#[test]
fn test_parameter_defaults_frozen() {
    let mut a = Assert::new();
    // Frozen parameter defaults are meant to error on mutation, check that
    a.module("f.bzl", "def f(x, xs = []):\n xs.append(x)\n return xs");
    // It works if we call it with an explicit parameter
    a.is_true("load('f.bzl', 'f')\nf(1, [2]) == [2, 1]");
    // But fails if we don't, with a frozen error
    a.fail("load('f.bzl', 'f')\nf(1) == [1]", "Immutable");
}

#[test]
fn test_arguments() {
    fn f(x: &str) -> String {
        format!(
            "
def f(a, b, c=5):
    return a * b + c
def g(a=1, b=2):
    return a+b
def h(a=1, *, b=2):
    return a+b
{}",
            x
        )
    }
    assert::is_true(&f("f(*[2, 3]) == 11"));
    assert::is_true(&f("f(*[2, 3, 7]) == 13"));
    assert::fail(&f("f(*[2])"), "Missing parameter");
    assert::is_true(&f("f(**{'b':3, 'a':2}) == 11"));
    assert::is_true(&f("f(**{'c':7, 'a':2, 'b':3}) == 13"));
    assert::fail(&f("f(**{'a':2})"), "Missing parameter");
    assert::fail(&f("f(**{'c':7, 'a':2, 'b':3, 'd':5})"), "extra named");
    assert::fail(&f("f(1, a=1, b=2)"), "occurs both");
    assert::fail(&f("g(a=1,*[2])"), "occurs both");
    assert::fail(&f("h(1, 2)"), "extra positional");
    assert::is_true(&f("h(2, b=3) == 5"));
    assert::is_true(&f("h(a=2, b=3) == 5"));
    assert::fail(
        &f("def bad(x, *, *args):\n  pass"),
        "parameter after another",
    );
}

#[test]
fn test_compiled_literals() {
    assert::is_true(
        "
def f():
    return [[]]
y = f()
y.append(1)
y == [[],1]",
    );
    assert::is_true(
        "
def f():
    return {1:2}
y = f()
y[3] = 4
y == {1:2, 3:4}",
    );
    // This test breaks if we compile constants deep compile the literals
    // and don't deep thaw them
    assert::is_true(
        "
def f():
    return [[]]
y = f()[0]
y.append(1)
y == [1]",
    );
}

#[test]
fn test_frozen_iteration() {
    // nested iteration
    assert::is_true(
        r#"
def loop():
    xs = [1, 2, 3]
    z = 0
    for x in xs:
        for y in xs:
            z += x + y
    return z
loop() == 36"#,
    );
    // iterate, mutate, iterate
    assert::is_true(
        r#"
def loop():
    y = 0
    xs = [1, 2, 3]
    for x in xs:
        y += x
    xs.append(4)
    for x in xs:
        y += x
    return y
loop() == 16"#,
    );
    // iterate and mutate at the same time
    assert::fail(
        r#"
def loop():
    xs = [1, 2, 3]
    for x in xs:
        if len(xs) == 3:
            xs.append(4)
loop()"#,
        "mutate an iterable",
    );
}

#[test]
fn test_lvalue_once() {
    assert::is_true(
        r#"
ys = [1]
xs = [1,2,3,4]

def f():
    return ys[0]

def g():
    ys[0] = 2;
    return 10

xs[f()] += g()
# f must be evaluated first, and only once
xs == [1,12,3,4]
"#,
    );
    assert::is_true(
        r#"
ys = [1]
xs = [1,2,3,4]

def f():
    return ys[0]

def g():
    ys[0] = 2;
    return 10

xs[f()] = g()
xs == [1, 2, 10, 4]
"#,
    );
}

#[test]
fn test_add_assign() {
    // += behaves differently on different types
    assert::pass(
        r#"
x = 1
x += 8
assert_eq(x, 9)"#,
    );
    assert::pass(
        r#"
orig = [1, 2]
x = orig
x += [3]
assert_eq(x, [1, 2, 3])
assert_eq(orig, [1, 2, 3])
"#,
    );
    assert::pass(
        r#"
orig = (1, 2)
x = orig
x += (3,)
assert_eq(x, (1, 2, 3))
assert_eq(orig, (1, 2))
"#,
    );
    assert::fail(
        r#"
x = {1: 2}
x += {3: 4}
"#,
        "not supported",
    );
    assert::pass(
        r#"
x = [1, 2]
x[0] += 5
assert_eq(x, [6, 2])
"#,
    );
    assert::pass(
        r#"
x = {1: 2}
x[1] += 5
assert_eq(x, {1: 7})
"#,
    );
    assert::fail(
        r#"
def foo():
    xs = [1, 2]
    for x in xs:
        xs += [1]
        break
foo()
"#,
        "mutate an iterable",
    );
    assert::fail(
        r#"
xs = (1, 2)
xs[1] += 1
"#,
        "Immutable",
    );
}

#[test]
fn test_compound_assignment() {
    assert::pass(
        r#"
x = 1
x <<= 8
assert_eq(x, 256)"#,
    );
    assert::pass(
        r#"
x = 1
x ^= 8
assert_eq(x, 9)"#,
    );
}

#[test]
fn test_self_mutate_list() {
    // Check functions that mutate and access self on lists
    assert::is_true(
        r#"
xs = [1, 2, 3]
xs.extend(xs)
xs == [1, 2, 3, 1, 2, 3]
"#,
    );
    assert::is_true(
        r#"
xs = [1, 2, 3]
xs += xs
xs == [1, 2, 3, 1, 2, 3]
"#,
    );
    assert::fail(
        r#"
xs = [1, 2, 3]
xs.pop(xs)
"#,
        "not supported",
    );
    assert::fail(
        r#"
xs = [1, 2, 3]
xs.remove(xs)
"#,
        "not found in list",
    );
    assert::is_true(
        r#"
xs = [1, 2, 3]
xs.append(xs)
xs.remove(xs)
xs == [1, 2, 3]
"#,
    )
}

#[test]
fn test_export_as() {
    use crate as starlark;
    use crate::values::{
        AllocValue, Freezer, Heap, ImmutableValue, MutableValue, TypedValue, Value, Walker,
    };
    use gazebo::any::AnyLifetime;

    #[derive(AnyLifetime, Debug)]
    struct Exporter {
        mutable: bool,
        named: String,
        value: i32,
    }

    impl TypedValue<'_> for Exporter {
        starlark_type!("exporter");

        fn collect_repr(&self, collector: &mut String) {
            collector.push_str(&self.named);
            collector.push('=');
            collector.push_str(&self.value.to_string());
        }
        fn naturally_mutable(&self) -> bool {
            self.mutable
        }
    }

    impl AllocValue<'_> for Exporter {
        fn alloc_value(self, heap: &Heap) -> Value {
            heap.alloc_mutable(self)
        }
    }

    impl MutableValue<'_> for Exporter {
        fn freeze(mut self: Box<Self>, _freezer: &Freezer) -> Box<dyn ImmutableValue> {
            self.mutable = false;
            self
        }

        unsafe fn walk(&mut self, _walker: &Walker) {}

        fn export_as(&mut self, _heap: &Heap, variable_name: &str) {
            self.named = variable_name.to_owned();
        }
    }

    impl ImmutableValue for Exporter {}

    #[starlark_module]
    fn exporter(builder: &mut GlobalsBuilder) {
        fn exporter(value: i32) -> Exporter {
            Ok(Exporter {
                mutable: true,
                named: "unnamed".to_owned(),
                value,
            })
        }
    }

    let mut a = Assert::new();
    a.globals_add(exporter);
    a.module(
        "a",
        "x = exporter(1); y = x; longer_name = exporter(2); arrayed = [exporter(3)]",
    );
    // could reasonably be x=1 or y=1 twice, since the order
    // of calls to export_as is not defined
    let opt1 = "(x=1, x=1, longer_name=2, unnamed=3)".to_owned();
    let opt2 = opt1.replace("x=", "y=");

    a.is_true(&format!(
        r#"
load('a', 'x', 'y', 'longer_name', 'arrayed')
v = str((x, y, longer_name, arrayed[0]))
v == '{}' or v == '{}'"#,
        opt1, opt2
    ))
}

#[test]
// Test that we can express something that loads symbols into the exported module
fn test_load_symbols() {
    #[starlark_module]
    fn module(builder: &mut GlobalsBuilder) {
        fn load_symbol(name: &str, value: Value<'v>) -> NoneType {
            ctx.set_module_variable_at_some_point(name, value, heap)?;
            Ok(NoneType)
        }
    }

    let mut a = Assert::new();
    a.globals_add(module);
    a.module("a", "load_symbol('x', 6*7)");
    a.is_true("load('a', 'x'); x == 42")
}

#[test]
// Test that we can express something that loads symbols into the exported module,
// but not using the very dubious `set_module_variable_at_some_point`.
fn test_load_symbols_extra() -> anyhow::Result<()> {
    #[starlark_module]
    fn module(builder: &mut GlobalsBuilder) {
        fn load_symbol(name: &str, value: Value<'v>) -> NoneType {
            let extra = ctx.extra_v.unwrap().downcast_ref::<Extra<'v>>().unwrap();
            extra.0.lock().unwrap().insert(name.to_owned(), value);
            Ok(NoneType)
        }
    }

    #[derive(AnyLifetime, Default)]
    struct Extra<'v>(Arc<Mutex<HashMap<String, Value<'v>>>>);

    let mut a = Assert::new();
    a.globals_add(module);
    let modu = Module::new();
    let globals = a.get_globals();
    let mut ctx = Evaluator::new(&modu, &globals);
    let extra = Extra::default();
    ctx.extra_v = Some(&extra);
    ctx.eval_module(AstModule::parse(
        "a",
        "load_symbol('x', 6*7)".to_owned(),
        &Dialect::Extended,
    )?)?;

    for (name, value) in extra.0.lock().unwrap().iter() {
        modu.set(name, *value);
    }
    a.module_add("a", modu.freeze());
    a.is_true("load('a', 'x'); x == 42");
    Ok(())
}

#[test]
fn test_static_name_checks() {
    let a = Assert::new();
    a.fail(
        r#"
def f():
    no_name()
True"#,
        "no_name",
    );
}

#[test]
fn test_not_hashable() {
    assert::fail(
        r#"
x = {}
y = {}
x[y] = 1
"#,
        "not hashable",
    );
    assert::fail(
        r#"
x = {'x': 1}
y = {}
x.get(y)
"#,
        "not hashable",
    );
    assert::fail(
        r#"
x = {'x': 1}
y = {}
x[y]
"#,
        "not hashable",
    );
}

#[test]
fn test_repr_str() {
    #[derive(AnyLifetime, Debug)]
    struct Foo(Option<usize>);

    #[starlark_module]
    fn module(builder: &mut GlobalsBuilder) {
        fn mk_foo() -> StarlarkAny {
            Ok(StarlarkAny::new(Foo(Some(42))))
        }
    }

    let mut a = Assert::new();
    a.globals_add(module);
    a.pass("assert_eq(repr(mk_foo()), 'Foo(Some(42))')");
}

#[test]
fn test_equality() {
    assert::all_true(
        r#"
None == None
True == True
True != False
1 == 1
1 != 2
"test" == "test"
"test" != "x"
[1, 2] == [1, 2]
[1, 3] != [1, 2]
[1, 3] != [1, 3, 4]
(1, 2) == (1, 2)
(1, 3) != (1, 2)
(1, 3) != (1, 3, 4)
range(4) == range(0, 4, 1)
range(4) != range(0, 4, 2)
range(4) != [0,1,2,3,4]
{1: 2} == {1: 2}
{1: 2} != {}
{1: 2, 3: 4} == {1: 2, 3: 4}
{1: 2, 3: 4} == {3: 4, 1: 2}  # Spec is a little ambiguous here
repr == repr
repr != str
[].copy != [1].copy
x = []; x.copy != x.copy
x = []; y = x.copy; y == y
x = repr; y = repr; x == y
"#,
    );
}

#[test]
fn test_comparison() {
    assert::all_true(
        r#"
False < True
1 < 2
"test" < "x"
[1, 3] > [1, 2]
[1, 3] < [1, 3, 4]
(1, 3) > (1, 2)
(1, 3) < (1, 3, 4)
"#,
    );
    assert::fail("None < None", "`compare` not supported");
    assert::fail("(None, ) < (None, )", "`compare` not supported");
    assert::fail("x = (None,); x < x", "`compare` not supported");
    assert::fail("x = {}; x < x", "`compare` not supported");
    assert::fail("{} < {1: 2}", "`compare` not supported");
    assert::fail("range(1) < range(2)", "`compare` not supported");
    assert::fail("repr < str", "`compare` not supported");
}

#[test]
fn test_frozen_hash() {
    let exprs = &["\"test\"", "\"x\""];
    let mut a = Assert::new();
    a.module(
        "m",
        &format!(
            r#"
dict = {{x:len(x) for x in [{}]}}
"#,
            exprs.join(",")
        ),
    );
    a.pass(&format!(
        r#"
load('m', frozen_dict='dict')
values = [{}]
assert_eq(all([frozen_dict[x] != None for x in values]), True)
"#,
        exprs.join(","),
    ));
}

#[test]
fn test_function_to_name() {
    let mut a = Assert::new();
    a.module(
        "x",
        r#"
def mine():
    pass
names = {repr: "repr", str: "str", mine: "mine"}
assert_eq(names[repr], "repr")
assert_eq(names[mine], "mine")
assert_eq(names[str], "str")
"#,
    );
    a.pass(
        r#"
load("x", "mine", "names")
assert_eq(names[repr], "repr")
assert_eq(names[mine], "mine")
assert_eq(names[str], "str")
"#,
    );
}

#[test]
// Check that errors print out "nicely" - can be used to view it.
// First set `display` to `true` then run:
//
// > EYEBALL=1 cargo test -p starlark eyeball -- --nocapture
fn test_eyeball() {
    let display = std::env::var("EYEBALL") == Ok("1".to_owned());

    let mut a = Assert::new();
    a.module(
        "imported",
        r#"
# blank lines to make line numbers bigger and more obvious
#
#
#
#
x = []
def add2(z):
  add(z)
def add(z):
  x.append(z)"#,
    );
    let diag = a.fail(
        r#"
load('imported', 'add2')
def add3(z):
    add2(z)
add3(8)"#,
        "Immutable",
    );
    if display {
        eprint_error(&diag)
    }
    assert_eq!(
        &format!("\n{}", diag),
        r#"
* assert.bzl.add3(z) (called from assert.bzl:5:1: 5:8)
* imported.bzl.add2(z) (called from assert.bzl:4:5: 4:12)
* imported.bzl.add(z) (called from imported.bzl:9:3: 9:9)
* append(this, el) (called from imported.bzl:11:3: 11:14)
error: Immutable
  --> imported.bzl:11:3
   |
11 |   x.append(z)
   |   ^^^^^^^^^^^
   |
"#
    );
}

#[test]
fn test_callstack() {
    // Make sure that even for native functions that fail, the
    // name of the function is on the call stack.
    let d = assert::fail(
        r#"
def f():
    fail("bad")
f()
"#,
        "bad",
    );
    assert!(d.to_string().contains("* fail(msg)"));
}

#[test]
fn test_compare() {
    assert::fail("1 > False", "Operation `==` not supported");
    assert::is_true("[1, 2] == [1, 2]");
    assert::is_true("1 != True");
    assert::is_true("not (None == [1])");
    assert::is_true(
        r#"
xs = [1]
xs[0] = xs
xs == xs
"#,
    );
    assert::is_true(
        r#"
ys = [1]
xs = [ys]
ys[0] = xs
xs == xs
"#,
    );
    assert::fail(
        r#"
ys = [1]
xs = [ys]
ys[0] = xs
xs == ys
"#,
        "recursion",
    );
}

#[test]
fn test_load_reexport() {
    let mut a = Assert::new();
    a.dialect_set(|d| d.enable_load_reexport = true);
    a.module("a", "x = 1");
    a.module("b", "load('a', 'x')");
    a.pass("load('b', 'x')\nassert_eq(x, 1)");

    let mut a = Assert::new();
    a.dialect_set(|d| d.enable_load_reexport = false);
    a.module("a", "x = 1");
    a.module("b", "load('a', 'x')");
    a.fail("load('b', 'x')\nassert_eq(x, 1)", "Variable `x` not found");
}

#[test]
fn test_display_debug() {
    let heap = Heap::new();
    let val = heap.alloc((vec![1, 2], "test", true));
    assert_eq!(format!("{}", val), "([1, 2], \"test\", True)");
    assert_eq!(val.to_repr(), "([1, 2], \"test\", True)");
    assert_eq!(val.to_str(), "([1, 2], \"test\", True)");
    assert_eq!(
        format!("{:?}", val),
        "Value(TupleGen { content: [Value(ListGen { content: [Value(1), Value(2)] }), Value(\"test\"), Value(true)] })"
    );
    assert_eq!(
        format!("{:#?}", val),
        r#"Value(
    TupleGen {
        content: [
            Value(
                ListGen {
                    content: [
                        Value(
                            1,
                        ),
                        Value(
                            2,
                        ),
                    ],
                },
            ),
            Value(
                "test",
            ),
            Value(
                true,
            ),
        ],
    },
)"#
    );

    let val = heap.alloc("test");
    assert_eq!(format!("{}", val), "test");
    assert_eq!(val.to_repr(), "\"test\"");
    assert_eq!(val.to_str(), "test");
    assert_eq!(format!("{:?}", val), "Value(\"test\")");
    assert_eq!(format!("{:#?}", val), "Value(\n    \"test\",\n)");
}

#[test]
fn test_argument_evaluation_order() {
    assert::pass(
        r#"
r = []

def id(x):
    r.append(x)
    return x

def f(*args, **kwargs):
    return (args, kwargs)

y = f(id(1), id(2), x=id(3), *[id(4)], **dict(z=id(5)))
assert_eq(y, ((1, 2, 4), dict(x=3, z=5)))
assert_eq(r, [1,2,3,4,5])
"#,
    );
}

#[test]
fn test_escape_characters() {
    // Test cases from the Starlark spec
    assert_eq!(
        assert::pass(r#"'\a\b\f\n\r\t\v'"#).to_string(),
        "\x07\x08\x0C\x0A\x0D\x09\x0B"
    );
    assert_eq!(assert::pass(r#"'\0'"#).to_string(), "\x00");
    assert_eq!(assert::pass(r#"'\12'"#).to_string(), "\n");
    assert_eq!(assert::pass(r#"'\101-\132'"#).to_string(), "A-Z");
    // 9 is not an octal digit, so it terminates early
    assert_eq!(assert::pass(r#"'\119'"#).to_string(), "\t9");
    assert_eq!(assert::pass(r#"'\117'"#).to_string(), "O");
    assert_eq!(assert::pass(r#"'\u0041'"#).to_string(), "A");
    assert_eq!(assert::pass(r#"'\u0414'"#).to_string(), "Д");
    assert_eq!(assert::pass(r#"'\u754c'"#).to_string(), "界");
    assert_eq!(assert::pass(r#"'\U0001F600'"#).to_string(), "😀");
}

#[test]
fn test_deallocation() {
    // Check that we really do deallocate values we create
    static COUNT: Lazy<AtomicUsize> = Lazy::new(|| AtomicUsize::new(0));

    #[derive(Default, Debug)]
    struct Dealloc;

    impl Drop for Dealloc {
        fn drop(&mut self) {
            COUNT.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[starlark_module]
    fn globals(builder: &mut GlobalsBuilder) {
        fn mk() -> StarlarkAny {
            Ok(StarlarkAny::new(Dealloc))
        }
    }

    COUNT.store(0, Ordering::SeqCst);
    let mut a = Assert::new();
    a.disable_gc();
    a.globals_add(globals);
    a.module("test", "x = [mk(), mk()]\ndef y(): return mk()");
    a.pass(
        r#"
load("test", "x", "y")
z = x[1]
q = mk()
r = [y(), mk()]
"#,
    );
    // The three that were run in pass should have gone
    assert_eq!(COUNT.load(Ordering::SeqCst), 3);
    mem::drop(a);
    // Now the frozen ones should have gone too
    assert_eq!(COUNT.load(Ordering::SeqCst), 5);
}

#[test]
fn test_not_in_unhashable() {
    // Note that [] can't be hashed
    assert::fail("[] not in {123: 456}", "not hashable");
}

#[test]
fn test_comprehension_blocks() {
    assert::fail(
        r#"
x = [1, 2]
res = [x for _ in [3] for x in x]
assert_eq(res, [1,2])
"#,
        "variable `x` referenced before assignment",
    );
}

#[test]
fn test_in_range() {
    // Go Starlark considers this a type error (I think that is a mistake)
    assert::all_true(
        r#"
not (True in range(3))
not ("one" in range(10))
"#,
    );
}

#[test]
fn test_dict_with_duplicates() {
    // In Starlark spec this is a runtime error. In Python it's fine.
    // We make it a runtime error, plus have a lint that checks for it statically.
    assert::fails("{40+2: 2, 6*7: 3}", &["key repeated", "42"]);
    // Also check we fail if the entire dictionary is static (a different code path).
    assert::fails("{42: 2, 42: 3}", &["key repeated", "42"]);
}

#[test]
fn test_self_assign() {
    // In Go Starlark this works.
    // Doesn't seem unreasonable.
    assert::fail("x = [1,2]\na, x[0] = x", "mutate an iterable");
    assert::fail("x = {0:0,1:1}\na, x[0] = x", "mutate an iterable");
}

#[test]
fn test_go() {
    macro_rules! test_case {
        ($name:expr) => {
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/testcases/eval/go/",
                $name,
            ))
        };
    }

    fn ignore_bad_lines(x: &str, bad: &[&str]) -> String {
        x.lines()
            .filter(|x| !bad.iter().any(|b| x.contains(b)))
            .join("\n")
    }

    // The data for these tests was taken from
    // https://github.com/google/starlark-go/blob/e81fc95f7bd5bb1495fe69f27c1a99fcc77caa48/starlark/testdata/

    let assert = Assert::new();
    assert.conformance_except(
        test_case!("assign.star"),
        &[
            "hasfields()", // Not sure what this is, but we don't support
        ],
    );
    // Skip benchmark.star, for benchmarking not testing
    assert.conformance(&ignore_bad_lines(
        test_case!("bool.star"),
        &[
            "0.0", // Floats, unsupported
        ],
    ));
    assert.conformance(&ignore_bad_lines(
        test_case!("builtin.star"),
        &[
            "2.0",                   // Floats, unsupported
            "[] not in {123: \"\"}", // We disagree, see test_not_in_unhashable
            // Exponents, unsupported
            "1e15",
            "1e100",
            // Set, unsupported
            "set(",
            "(myset)",
            "(myset,",
            // Has fields, unsupported
            "hasfields()",
            "(hf)",
            "(hf,",
            "(hf,",
            "hf.",
            "(setfield,",
            // test_in_range
            "True in range(3)",
            "\"one\" in range(10)",
            // Starlark spec demands elems() return a list of int, Go returns list of string
            "\"abc\".elems()",
            "\"def\".elems()",
            "\"hijk\".elems()",
            "(\"a\", \"d\", \"h\")", // end of a multiline that tests elems()
            // We added copy, which throws off the assert
            "dir({})[:3]",
            "dir([])[:3]",
        ],
    ));
    assert.conformance(test_case!("control.star"));
    assert.conformance_except(
        &ignore_bad_lines(
            test_case!("dict.star"),
            &[
                "unknown binary op: dict \\\\+ dict",   // We support {} + {}
                "cannot insert into frozen hash table", // We don't actually have freeze
                "cannot clear frozen hash table",
                "a, x[0] = x",     // Our bug, see test_self_assign
                "assert.eq(a, 1)", // End of the test above
                "assert.eq(x, {1: 2, 2: 4, 0: 2})",
            ],
        ),
        &[
            "Verify position of an \"unhashable key\"", // FIXME: We should give a better error message
            "Verify position of a \"duplicate key\"",   // FIXME: Give a better line number
            "Verify position of an \"unhashable key\"", // FIXME: we should do better
        ],
    );
    // Skip float.star, since we don't support floats
    assert.conformance(&ignore_bad_lines(
        test_case!("function.star"),
        &[
            "eq(str",             // We render function names differently
            "frozen list",        // Our freeze does nothing
            "called recursively", // We allow recursion
            "hf",                 // We don't support hasfield
        ],
    ));
    // Skip int.star, a lot of bit mask stuff, floats and int's outside our range
    // Skip list.star, our strings disagree about whether they are lists of codepoints or lists of 1-char strings
    assert.conformance_except(
        &ignore_bad_lines(
            test_case!("misc.star"),
            &[
                "2.0",                          // We don't support float
                "'<built-in function freeze>'", // Different display of functions
            ],
        ),
        &[
            "cyclic data structures", // We overflow on some of these
        ],
    );
    // Skip module.star, we don't support modules
    // Skip paths.star, a path support library, not tests
    // Skip recursion.star, we don't support `while` loops, which is what this mostly tests
    // Skip set.star, we don't support set
    // Skip string.star, our String's are fundamentally different
    assert.conformance(
        // Our elems() works differently
        &ignore_bad_lines(
            &test_case!("tuple.star").replace("\"abc\".elems()", "[\"a\",\"b\",\"c\"]"),
            &[
                "1000000 * 1000000", // Some tests check that you can't create too large tuples, but that's not principled, so we allow it
                // But it takes approximately forever, so doing it is a bad idea.
            ],
        ),
    );
}
