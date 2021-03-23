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
    self as starlark,
    environment::GlobalsBuilder,
    eval::Parameters,
    values::{
        function::{FunctionInvoker, FUNCTION_VALUE_TYPE_NAME},
        AllocValue, Freezer, FrozenValue, Heap, ImmutableValue, MutableValue, TypedValue, Value,
        ValueLike, Walker,
    },
};
use gazebo::any::AnyLifetime;
use std::collections::HashSet;

#[starlark_module]
pub fn global(builder: &mut GlobalsBuilder) {
    fn filter(func: Value, seq: Value) -> Vec<Value<'v>> {
        let mut res = Vec::new();

        for v in &seq.iterate(heap)? {
            if func.is_none() {
                if !v.is_none() {
                    res.push(v);
                }
            } else {
                let mut inv = func.new_invoker(heap)?;
                inv.push_pos(v);
                if inv.invoke(func, None, ctx)?.to_bool() {
                    res.push(v);
                }
            }
        }
        Ok(res)
    }

    fn map(func: Value, seq: Value) -> Vec<Value<'v>> {
        let mut res = Vec::new();
        for v in &seq.iterate(heap)? {
            let mut inv = func.new_invoker(heap)?;
            inv.push_pos(v);
            res.push(inv.invoke(func, None, ctx)?);
        }
        Ok(res)
    }

    fn partial(func: Value, args: Value, kwargs: Value) -> Partial<Value<'v>> {
        // TODO: use func name (+ something?)
        let name = "partial_closure".to_owned();
        let mut signature = Parameters::with_capacity(name, 2);
        signature.args("args");
        signature.kwargs("kwargs");
        Ok(Partial {
            func,
            args,
            kwargs,
            signature,
        })
    }

    /// Print the value with full debug formatting. The result may not be stable over time,
    /// mostly intended for debugging purposes.
    fn debug(val: Value) -> String {
        Ok(format!("{:?}", val))
    }

    /// Remove duplicates in a list. Uses identity of value (pointer),
    /// rather than by equality.
    fn dedupe(val: Value) -> Value<'v> {
        let mut seen = HashSet::new();
        let mut res = Vec::new();
        for v in &val.iterate(heap)? {
            let p = v.ptr_value();
            if !seen.contains(&p) {
                seen.insert(p);
                res.push(v);
            }
        }
        Ok(heap.alloc(res))
    }
}

#[derive(Debug)]
struct Partial<V> {
    func: V,
    args: V,
    kwargs: V,
    signature: Parameters<V>,
}

unsafe impl<'v> AnyLifetime<'v> for Partial<Value<'v>> {
    any_lifetime_body!(Partial<Value<'static>>);
}
any_lifetime!(Partial<FrozenValue>);

impl<'v> AllocValue<'v> for Partial<Value<'v>> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_mutable(self)
    }
}

impl<'v> MutableValue<'v> for Partial<Value<'v>> {
    fn freeze<'fv>(self: Box<Self>, freezer: &'fv Freezer) -> Box<dyn ImmutableValue<'fv> + 'fv> {
        box Partial {
            func: self.func.freeze(freezer),
            args: self.args.freeze(freezer),
            kwargs: self.kwargs.freeze(freezer),
            signature: self.signature.freeze(freezer),
        }
    }

    unsafe fn walk(&mut self, walker: &Walker<'v>) {
        walker.walk(&mut self.func);
        walker.walk(&mut self.args);
        walker.walk(&mut self.kwargs);
        self.signature.walk(walker);
    }
}

impl<'v> AllocValue<'v> for Partial<FrozenValue> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_immutable(self)
    }
}

impl<'v> ImmutableValue<'v> for Partial<FrozenValue> {}

impl<'v, V: ValueLike<'v>> TypedValue<'v> for Partial<V>
where
    Self: AnyLifetime<'v>,
{
    starlark_type!(FUNCTION_VALUE_TYPE_NAME);

    fn is_function(&self) -> bool {
        true
    }

    fn new_invoker<'a>(
        &self,
        _me: Value<'v>,
        heap: &'v Heap,
    ) -> anyhow::Result<FunctionInvoker<'v, 'a>> {
        let mut inv = self.func.new_invoker(heap)?;
        inv.push_args(self.args.to_value(), heap);
        inv.push_kwargs(self.kwargs.to_value());
        Ok(inv)
    }

    fn collect_repr(&self, collector: &mut String) {
        collector.push_str("partial(");
        self.func.collect_repr(collector);
        collector.push_str(", *");
        self.args.collect_repr(collector);
        collector.push_str(", **");
        self.kwargs.collect_repr(collector);
        collector.push(')');
    }
}

#[cfg(test)]
mod tests {
    use crate::assert;

    #[test]
    fn test_filter() {
        assert::pass(
            r#"
def contains_hello(s):
    if "hello" in s:
        return True
    return False

def positive(i):
    return i > 0

assert_eq([], filter(positive, []))
assert_eq([1, 2, 3], filter(positive, [1, 2, 3]))
assert_eq([], filter(positive, [-1, -2, -3]))
assert_eq([1, 2, 3], filter(positive, [-1, 1, 2, -2, -3, 3]))
assert_eq(["hello world!"], filter(contains_hello, ["hello world!", "goodbye"]))
"#,
        );
    }

    #[test]
    fn test_map() {
        assert::pass(
            r#"
def double(x):
    return x + x

assert_eq([], map(int, []))
assert_eq([1,2,3], map(int, ["1","2","3"]))
assert_eq(["0","1","2"], map(str, range(3)))
assert_eq(["11",8], map(double, ["1",4]))
"#,
        );
    }

    #[test]
    fn test_partial() {
        assert::pass(
            r#"
def sum(a, b, *args, **kwargs):
    # print("a=%s b=%s args=%s kwargs=%s" % (a, b, args, kwargs))
    args = (a, b) + args
    return [args, kwargs]

# simple test
assert_eq(
    [(1, 2, 3), {"other": True, "third": None}],
    (partial(sum, 1, other=True))(2, 3, third=None))

# passing *args **kwargs to partial
assert_eq(
    [(1, 2, 3), {"other": True, "third": None}],
    (partial(sum, *[1], **{"other": True}))(2, 3, third=None))

# passing *args **kwargs to returned func
assert_eq(
    [(1, 2, 3), {"other": True, "third": None}],
    (partial(sum, other=True))(*[1, 2, 3], **{"third": None}))

# no args to partial
assert_eq(
    [(1, 2, 3), {"other": True, "third": None}],
    (partial(sum))(1, 2, 3, third=None, **{"other": True}))
"#,
        );
    }

    #[test]
    fn test_debug() {
        assert::pass(
            r#"assert_eq(debug([1,2]), "Value(ListGen { content: [FrozenValue(1), FrozenValue(2)] })")"#,
        );
    }

    #[test]
    fn test_dedupe() {
        assert::pass(
            r#"
assert_eq(dedupe([1,2,3]), [1,2,3])
assert_eq(dedupe([1,2,3,2,1]), [1,2,3])
a = [1]
b = [1]
assert_eq(dedupe([a,b,a]), [a,b])
"#,
        );
    }
}
