//! Tests for `def` decorators.

use crate::typing::tests::TypeCheck;

/// The return type of the decorator determines the type of the decorated name.
#[test]
fn test_decorator_replaces_type() {
    TypeCheck::new().ty("fn").check(
        "decorator_replaces_type",
        r#"
def actually_an_integer(f) -> int:
    return 42

@actually_an_integer
def fn(x: str) -> bool:
    return True
"#,
    );
}

/// An untyped decorator binds the name of the decorated function to typing.Any.
#[test]
fn untyped_returns_any() {
    TypeCheck::new().ty("fn").check(
        "decorator_without_type_hints_returns_any",
        r#"
def identity(f):
    return f

@identity
def fn(x: int) -> str:
    return str(x)

def fn_should_still_be_callable():
    fn(23)
"#,
    );
}

/// Stacked decorators: the outermost decorator's return type is the binding type.
#[test]
fn test_decorator_stacked_type() {
    TypeCheck::new().ty("fn").check(
        "decorator_stacked_type",
        r#"
def outer_dec(f) -> int:
    return 0

def inner_dec(f):
    return f

@outer_dec
@inner_dec
def fn(x: str) -> bool:
    return True
"#,
    );
}

/// A decorator factory: `@make_decorator(arg)` — the result of calling `make_decorator(arg)` is
/// applied as a decorator and the type of `fn` is the return type of the callable returned by
/// `make_decorator`.
#[test]
fn test_decorator_factory_type() {
    TypeCheck::new().ty("fn").check(
        "decorator_factory_type",
        r#"
def make_decorator(label: str) -> typing.Callable[[typing.Callable], str]:
    def decorator(f):
        f()
        return label
    return decorator

@make_decorator("hello")
def fn(x: int) -> int:
    return x
"#,
    );
}
