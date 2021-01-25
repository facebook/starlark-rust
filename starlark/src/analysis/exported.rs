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

use crate::syntax::{ast::Stmt, AstModule};
use codemap::SpanLoc;
use indexmap::IndexMap;

// Which symbols are exported by a module
pub fn exported_symbols(module: &AstModule) -> Vec<(SpanLoc, String)> {
    // Map since we only want to store the first of each export
    // IndexMap since we want the order to match the order they were defined in
    let mut result = IndexMap::new();
    module.statement.visit_stmt(|x| match &***x {
        Stmt::Assign(dest, _, _) => {
            dest.visit_expr_lvalue(|name| {
                result.entry(&name.node).or_insert(name.span);
            });
        }
        Stmt::Def(name, ..) => {
            result.entry(name).or_insert(name.span);
        }
        _ => {}
    });
    result
        .into_iter()
        .filter(|(name, _)| !name.starts_with('_'))
        .map(|(name, span)| (module.codemap.look_up_span(span), name.to_owned()))
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::syntax::{parse, Dialect};
    use gazebo::prelude::*;

    fn module(x: &str) -> AstModule {
        parse("X", x, &Dialect::Extended).unwrap()
    }

    #[test]
    fn test_lint_exported() {
        let res = exported_symbols(&module(
            r#"
load("test", "a")
def b(): pass
d = 1
def _e(): pass
d = 2
"#,
        ));
        assert_eq!(
            res.map(|(loc, name)| format!("{} {}", loc, name)),
            &["X:3:5: 3:6 b", "X:4:1: 4:2 d"]
        );
    }
}
