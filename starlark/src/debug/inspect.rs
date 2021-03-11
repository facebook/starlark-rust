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

use crate::{
    collections::SmallMap,
    eval::{
        def::{Def, FrozenDef},
        Evaluator, ScopeNames,
    },
    values::Value,
};
use gazebo::{cell::ARef, prelude::*};

pub fn inspect_stack(ctx: &Evaluator) -> Vec<String> {
    ctx.call_stack()
        .to_diagnostic_frames()
        .map(ToString::to_string)
}

pub(crate) fn to_scope_names<'v>(x: Value<'v>) -> Option<ARef<'v, ScopeNames>> {
    if let Some(x) = x.downcast_ref::<Def<'v>>() {
        Some(ARef::map(x, |x| x.scope_names()))
    } else if let Some(x) = x.downcast_ref::<FrozenDef>() {
        Some(ARef::map(x, |x| x.scope_names()))
    } else {
        None
    }
}

fn inspect_local_variables<'v>(ctx: &Evaluator<'v, '_>) -> Option<SmallMap<String, Value<'v>>> {
    // First we find the first entry on the call_stack which contains a Def (and thus has locals)
    let xs = ctx.call_stack().to_function_values();
    let names = xs.into_iter().rev().find_map(to_scope_names)?;
    let mut res = SmallMap::new();
    for (name, slot) in &names.mp {
        if let Some(v) = ctx.local_variables.get_slot(*slot) {
            res.insert(name.clone(), v);
        }
    }
    Some(res)
}

fn inspect_module_variables<'v>(ctx: &Evaluator<'v, '_>) -> SmallMap<String, Value<'v>> {
    let mut res = SmallMap::new();
    for (name, slot) in ctx.module_env.names().all_names() {
        if let Some(v) = ctx.module_env.slots().get_slot(slot) {
            res.insert(name, v);
        }
    }
    res
}

pub fn inspect_variables<'v>(ctx: &Evaluator<'v, '_>) -> SmallMap<String, Value<'v>> {
    inspect_local_variables(ctx).unwrap_or_else(|| inspect_module_variables(ctx))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{self as starlark, assert, environment::GlobalsBuilder, values::structs::Struct};

    #[starlark_module]
    fn debugger(builder: &mut GlobalsBuilder) {
        fn debug_inspect_stack() -> Vec<String> {
            Ok(inspect_stack(ctx))
        }

        fn debug_inspect_variables() -> Struct<'v> {
            Ok(Struct {
                fields: inspect_variables(ctx),
            })
        }
    }

    #[test]
    fn test_debug_stack() {
        let mut a = assert::Assert::new();
        a.globals_add(debugger);
        a.pass(
            r#"
def assert_stack(want):
    stack = debug_inspect_stack()
    assert_eq([x.split('(')[0] for x in stack[:-2]], want)

assert_stack([])

def f(): assert_stack(["assert.bzl.g", "assert.bzl.f"])
def g(): f()
g()
"#,
        );
    }

    #[test]
    fn test_debug_variables() {
        let mut a = assert::Assert::new();
        a.globals_add(debugger);
        a.pass(
            r#"
root = 12
_ignore = [x for x in [True]]
def f(x = 1, y = "test"):
    z = x + 5
    for _magic in [False, True]:
        continue
    assert_eq(debug_inspect_variables(), struct(x = 1, y = "hello", z = 6, _magic = True))
f(y = "hello")
assert_eq(debug_inspect_variables(), struct(root = 12, f = f, _ignore = [True]))
"#,
        );
    }
}
