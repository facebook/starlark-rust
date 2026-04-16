//! Runtime behavior tests for `def` decorators.

use crate::assert::Assert;

#[test]
fn test_decorator_identity() {
    Assert::new().pass(
        r#"
def identity(f):
    return f

@identity
def fn(input):
    return input

assert_eq(fn(7), 7)
assert_eq(fn("asdf"), "asdf")
"#,
    );
}

#[test]
fn test_decorator_replaces_name() {
    Assert::new().pass(
        r#"
def dec(f):
    return None

@dec
def fn():
    return "result of fn"

# the name "fn" is now bound to the return value of dec, instead of the def
assert_eq(fn, None)
"#,
    );
}

#[test]
fn test_decorator_evaluation_order() {
    Assert::new().pass(
        r#"
evaluation_order = []
execution_order = []

def dec(name):
    def named_dec(f):
        evaluation_order.append(name)
        return f
    return named_dec

@dec("a")
@dec("b")
@dec("c")
def my_func():
    pass

# evaluation order must be inside-out
assert_eq(evaluation_order, ["c", "b", "a"])
"#,
    );
}

#[test]
fn test_decorator_non_callable_fails() {
    Assert::new().fails(
        r#"
not_callable = 99

@not_callable
def should_fail():
    return
        "#,
        &["Operation `call()` not supported on type `int`"],
    );
}

#[test]
fn test_decorator_forwards_args() {
    Assert::new().pass(
        r#"
def logged(f):
    def wrapper(*args, **kwargs):
        return f(*args, **kwargs)
    return wrapper

@logged
def add(x, y):
    return x + y

assert_eq(add(3, 4), 7)
"#,
    );
}
