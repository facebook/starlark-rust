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

//! Test starlark-rust embedding.

use crate as starlark;
use crate::{
    assert,
    assert::Assert,
    environment::{Globals, GlobalsBuilder, Module},
    eval::Evaluator,
    syntax::{AstModule, Dialect},
    values::{any::StarlarkAny, none::NoneType, StarlarkValue, Value},
};
use gazebo::{any::AnyLifetime, cell::AsARef};
use std::{
    cell::RefCell,
    collections::HashMap,
    sync::{Arc, Mutex},
};

#[test]
fn test_export_as() {
    use crate as starlark;
    use crate::values::{
        AllocValue, ComplexValue, Freezer, Heap, SimpleValue, StarlarkValue, Trace, Value,
    };
    use gazebo::any::AnyLifetime;
    use std::fmt::Debug;

    #[derive(Debug, Trace)]
    struct Exporter<T> {
        // Either String or a RefCell therefore
        named: T,
        value: i32,
    }
    any_lifetime!(Exporter<RefCell<String>>);
    any_lifetime!(Exporter<String>);

    impl<'v, T: AsARef<String> + Debug> StarlarkValue<'v> for Exporter<T>
    where
        Self: AnyLifetime<'v>,
    {
        starlark_type!("exporter");

        fn collect_repr(&self, collector: &mut String) {
            collector.push_str(self.named.as_aref().as_str());
            collector.push('=');
            collector.push_str(&self.value.to_string());
        }

        fn export_as(&self, variable_name: &str, _eval: &mut Evaluator<'v, '_>) {
            if let Some(named) = self.named.as_ref_cell() {
                *named.borrow_mut() = variable_name.to_owned();
            }
        }
    }

    impl AllocValue<'_> for Exporter<RefCell<String>> {
        fn alloc_value(self, heap: &Heap) -> Value {
            heap.alloc_complex(self)
        }
    }

    impl<'v> ComplexValue<'v> for Exporter<RefCell<String>> {
        type Frozen = Exporter<String>;
        fn freeze(self, _freezer: &Freezer) -> anyhow::Result<Self::Frozen> {
            Ok(Exporter {
                named: self.named.into_inner(),
                value: self.value,
            })
        }
    }

    impl SimpleValue for Exporter<String> {}

    #[starlark_module]
    fn exporter(builder: &mut GlobalsBuilder) {
        fn exporter(value: i32) -> Exporter<RefCell<String>> {
            Ok(Exporter {
                named: RefCell::new("unnamed".to_owned()),
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
            eval.set_module_variable_at_some_point(name, value)?;
            Ok(NoneType)
        }
    }

    let mut a = Assert::new();
    a.globals_add(module);
    a.module("a", "load_symbol('x', 6*7)");
    a.is_true("load('a', 'x'); x == 42")
}

#[test]
fn test_load_public_symbols_does_not_reexport() -> anyhow::Result<()> {
    let mut a = Assert::new();

    let module_b = a.module("b", "x = 5");
    let module_a = Module::new();
    module_a.import_public_symbols(&module_b);
    a.module_add("a", module_a.freeze()?);
    // Trying to load a symbol transitively should fail.
    a.fail("load('a', 'x')", "Module symbol `x` is not exported");
    Ok(())
}

#[test]
// Test that we can express something that loads symbols into the exported module,
// but not using the very dubious `set_module_variable_at_some_point`.
fn test_load_symbols_extra() -> anyhow::Result<()> {
    #[starlark_module]
    fn module(builder: &mut GlobalsBuilder) {
        fn load_symbol(name: &str, value: Value<'v>) -> NoneType {
            let extra = eval.extra_v.unwrap().downcast_ref::<Extra<'v>>().unwrap();
            extra.0.lock().unwrap().insert(name.to_owned(), value);
            Ok(NoneType)
        }
    }

    #[derive(AnyLifetime, Default)]
    struct Extra<'v>(Arc<Mutex<HashMap<String, Value<'v>>>>);

    let modu = Module::new();
    let globals = GlobalsBuilder::extended().with(module).build();
    let mut eval = Evaluator::new(&modu, &globals);
    let extra = Extra::default();
    eval.extra_v = Some(&extra);
    eval.eval_module(AstModule::parse(
        "a",
        "load_symbol('x', 6*7)".to_owned(),
        &Dialect::Extended,
    )?)?;

    for (name, value) in extra.0.lock().unwrap().iter() {
        modu.set(name, *value);
    }
    let mut a = Assert::new();
    a.globals(globals);
    a.module_add("a", modu.freeze()?);
    a.is_true("load('a', 'x'); x == 42");
    Ok(())
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

// The example from the starlark_module documentation.
#[test]
fn test_starlark_module() {
    #[starlark_module]
    fn global(builder: &mut GlobalsBuilder) {
        fn cc_binary(name: &str, srcs: Vec<&str>) -> String {
            // real implementation may write it to a global variable
            Ok(format!("{:?} {:?}", name, srcs))
        }
    }

    let mut a = Assert::new();
    a.globals_add(global);
    let v = a.pass("cc_binary(name='star', srcs=['a.cc', 'b.cc'])");
    assert_eq!(
        v.value().unpack_str().unwrap(),
        r#""star" ["a.cc", "b.cc"]"#
    );
}

mod value_of {
    use super::*;
    use crate::{
        self as starlark,
        assert::Assert,
        environment::GlobalsBuilder,
        values::{dict::DictOf, list::ListOf, ValueOf},
    };
    use either::Either;
    use itertools::Itertools;

    // TODO(nmj): Figure out default values here. ValueOf<i32> = 5 should work.
    #[starlark_module]
    fn validate_module(builder: &mut GlobalsBuilder) {
        fn with_int(v: ValueOf<i32>) -> (Value<'v>, String) {
            Ok((*v, format!("{}", v.typed)))
        }
        fn with_int_list(v: ListOf<i32>) -> (Value<'v>, String) {
            let repr = v.to_vec().iter().join(", ");
            Ok((*v, repr))
        }
        fn with_list_list(v: ListOf<ListOf<i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_vec()
                .iter()
                .map(|l| l.to_vec().iter().join(", "))
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_dict_list(v: ListOf<DictOf<i32, i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_vec()
                .iter()
                .map(|l| {
                    l.to_dict()
                        .iter()
                        .map(|(k, v)| format!("{}: {}", k, v))
                        .join(", ")
                })
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_int_dict(v: DictOf<i32, i32>) -> (Value<'v>, String) {
            let repr = v
                .to_dict()
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v))
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_list_dict(v: DictOf<i32, ListOf<i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_dict()
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v.to_vec().iter().join(", ")))
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_dict_dict(v: DictOf<i32, DictOf<i32, i32>>) -> (Value<'v>, String) {
            let repr = v
                .to_dict()
                .iter()
                .map(|(k, v)| {
                    let inner_repr = v
                        .to_dict()
                        .iter()
                        .map(|(k2, v2)| format!("{}:{}", k2, v2))
                        .join(", ");
                    format!("{}: {}", k, inner_repr)
                })
                .join(" + ");
            Ok((*v, repr))
        }
        fn with_either(v: Either<i32, Either<String, ListOf<i32>>>) -> String {
            match v {
                Either::Left(i) => Ok(i.to_string()),
                Either::Right(nested) => match nested {
                    Either::Left(s) => Ok(s),
                    Either::Right(l) => Ok(l.to_repr()),
                },
            }
        }
    }

    // The standard error these raise on incorrect types
    const BAD: &str = "Type of parameter";

    #[test]
    fn test_value_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("(1, '1')", "with_int(1)");
        a.fail("with_int(None)", BAD);
    }

    #[test]
    fn test_list_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("([1, 2, 3], '1, 2, 3')", "with_int_list([1, 2, 3])");
        a.fail("with_int_list(1)", BAD);
        a.fail("with_int_list([1, 'foo'])", BAD);
        a.fail("with_int_list([[]])", BAD);

        a.eq(
            "([[1, 2], [3]], '1, 2 + 3')",
            "with_list_list([[1, 2], [3]])",
        );

        let expected = r#"([{1: 2, 3: 4}, {5: 6}], "1: 2, 3: 4 + 5: 6")"#;
        let test = r#"with_dict_list([{1: 2, 3: 4}, {5: 6}])"#;
        a.eq(expected, test);
    }

    #[test]
    fn test_dict_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("({1: 2}, '1: 2')", "with_int_dict({1: 2})");
        a.fail(r#"with_int_dict(1)"#, BAD);
        a.fail(r#"with_int_dict({1: "str"})"#, BAD);
        a.fail(r#"with_int_dict({1: {}})"#, BAD);

        let expected = r#"({1: [2, 3], 4: [5]}, "1: 2, 3 + 4: 5")"#;
        let test = r#"with_list_dict({1: [2, 3], 4: [5]})"#;
        a.eq(expected, test);

        let expected = r#"({1: {2: 3, 4: 5}, 6: {7: 8}}, "1: 2:3, 4:5 + 6: 7:8")"#;
        let test = r#"with_dict_dict({1: {2: 3, 4: 5}, 6: {7: 8}})"#;
        a.eq(expected, test);
    }

    #[test]
    fn test_either_of() {
        let mut a = Assert::new();
        a.globals_add(validate_module);
        a.eq("'2'", "with_either(2)");
        a.eq("'[2, 3]'", "with_either([2,3])");
        a.eq("'s'", "with_either('s')");
        a.fail("with_either(None)", BAD);
        a.fail("with_either({})", BAD);
    }
}

#[test]
fn test_derive_attrs() {
    #[derive(Debug, StarlarkAttrs)]
    struct Example {
        hello: String,
        #[starlark(skip)]
        answer: i64,
        #[starlark(clone)]
        nested: Nested,
    }
    starlark_simple_value!(Example);
    impl<'v> StarlarkValue<'v> for Example {
        starlark_type!("example");
        starlark_attrs!();
    }

    #[derive(Debug, Clone, StarlarkAttrs)]
    struct Nested {
        foo: String,
    }
    starlark_simple_value!(Nested);
    impl<'v> StarlarkValue<'v> for Nested {
        starlark_type!("nested");
        starlark_attrs!();
    }

    let mut a = Assert::new();
    a.globals_add(|gb| {
        gb.set(
            "example",
            Example {
                hello: "world".to_owned(),
                answer: 42,
                nested: Nested {
                    foo: "bar".to_owned(),
                },
            },
        )
    });
    a.eq("example.hello", "\"world\"");
    a.eq("dir(example)", "[\"hello\", \"nested\"]");
    a.is_true("not hasattr(example, \"answer\")");
    a.eq("example.nested.foo", "\"bar\"");
}

#[test]
fn test_eval_function() {
    let fun = assert::pass(
        r#"
def fun(a, *, y: "string", x = 1) -> "string":
    return str((a, y, x))
fun
"#,
    );
    let env = Module::new();
    let globals = Globals::standard();
    let mut eval = Evaluator::new(&env, &globals);
    let hello = env.heap().alloc("hello");
    let v = eval
        .eval_function(fun.value(), &[Value::new_int(8)], &[("y", hello)])
        .unwrap();
    assert_eq!(v.unpack_str(), Some("(8, \"hello\", 1)"))
}
