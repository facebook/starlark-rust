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
    debug::to_scope_names,
    eval::{eval_module, EvaluationContext},
    syntax::{parse, Dialect},
    values::Value,
};
use std::{collections::HashMap, mem};

/// Evaluate an expression in a context. Attempt to map variables over and back again.
/// Lots of health warnings on this code. Might not work with frozen modules, unassigned variables,
/// nested definitions etc. All are solvable, with increasing levels of effort.
/// It would be a bad idea to rely on the results after evaluating stuff randomly.
pub fn evaluate<'v>(code: &str, ctx: &mut EvaluationContext<'v, '_>) -> anyhow::Result<Value<'v>> {
    let ast = parse("interactive", code, &Dialect::Extended)?;

    // Everything must be evaluated with the current heap (or we'll lose memory), which means
    // the current module (ctx.module_env).
    // We also want access to the module variables (fine), the locals (need to move them over),
    // and the frozen variables (move them over).
    // Afterwards, we want to put everything back - locals can move back to locals, modules
    // can stay where they are, but frozen values are discarded.

    // We want all the local variables to be available to the module, so we capture
    // everything before, shove the local variables into the module, and then revert after
    let original_module: HashMap<String, Option<Value<'v>>> = ctx
        .module_env
        .names()
        .all_names()
        .iter()
        .map(|(name, slot)| (name.clone(), ctx.module_env.slots().get_slot(*slot)))
        .collect();

    // Push all the frozen variables into the module
    if let Some(frozen) = &ctx.module_variables {
        for (name, slot) in frozen.0.names.symbols() {
            if let Some(value) = frozen.get_slot(*slot) {
                ctx.module_env.set(name, value.to_value())
            }
        }
    }

    // Push all local variables into the module
    let locals = ctx
        .call_stack()
        .to_function_values()
        .into_iter()
        .rev()
        .find_map(to_scope_names);
    if let Some(names) = &locals {
        for (name, slot) in &names.mp {
            if let Some(value) = ctx.local_variables.get_slot(*slot) {
                ctx.module_env.set(name, value)
            }
        }
    }

    let orig_is_module_scope = mem::replace(&mut ctx.is_module_scope, true);
    let orig_module_variables = mem::replace(&mut ctx.module_variables, None);
    let res = eval_module(ast, ctx);
    ctx.is_module_scope = orig_is_module_scope;
    ctx.module_variables = orig_module_variables;

    // Now put the Module back how it was before we started, as best we can
    // and move things into locals if that makes sense
    if let Some(names) = &locals {
        for (name, slot) in &names.mp {
            if let Some(value) = ctx.module_env.get(name) {
                ctx.local_variables.set_slot(*slot, value)
            }
        }
        for (name, slot) in ctx.module_env.names().all_names() {
            match original_module.get(&name) {
                None => ctx.module_env.names().hide_name(&name),
                Some(Some(value)) => ctx.module_env.slots().set_slot(slot, *value),
                _ => {} // No way to unassign a previously assigned value yet
            }
        }
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{self as starlark, assert, environment::GlobalsBuilder};
    use itertools::Itertools;

    #[starlark_module]
    fn debugger(builder: &mut GlobalsBuilder) {
        fn debug_evaluate(code: &str) -> Value<'v> {
            evaluate(code, ctx)
        }
    }

    #[test]
    fn test_debug_evaluate() {
        let mut a = assert::Assert::new();
        a.globals_add(debugger);
        let check = r#"
assert_eq(debug_evaluate("1+2"), 3)
x = 10
assert_eq(debug_evaluate("x"), 10)
assert_eq(debug_evaluate("x = 5"), None)
assert_eq(x, 5)
y = [20]
debug_evaluate("y.append(30)")
assert_eq(y, [20, 30])
"#;
        // Check evaluation works at the root
        a.pass(check);
        // And inside functions
        a.pass(&format!(
            "def local():\n{}\nlocal()",
            check.lines().map(|x| format!("    {}", x)).join("\n")
        ));

        // Check we get the right stack frames
        a.pass(
            r#"
def foo(x, y, z):
    return bar(y)
def bar(x):
    return debug_evaluate("x")
assert_eq(foo(1, 2, 3), 2)
"#,
        );

        // Check we can access module-level and globals
        a.pass(
            r#"
x = 7
def bar(y):
    return debug_evaluate("x + y")
assert_eq(bar(4), 4 + 7)
"#,
        );

        // Check module-level access works in imported modules
        a.module(
            "test",
            r#"
x = 7
z = 2
def bar(y):
    assert_eq(x, 7)
    debug_evaluate("x = 20")
    assert_eq(x, 7) # doesn't work for frozen variables
    return debug_evaluate("x + y + z")
"#,
        );
        a.pass("load('test', 'bar'); assert_eq(bar(4), 4 + 7 + 2)");
    }
}
