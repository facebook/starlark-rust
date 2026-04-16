# Decorators

The Starlark `decorators` extension enables [PEP 614](https://peps.python.org/pep-0614/)-style syntax.

Basically, it enables code like this:

```python
@asdf
def foo():
    ...
```

... which is equivalent to this:

```python
def foo():
    ...

foo = asdf(foo)
```

All valid Starlark expressions (e.g. variables, calls, access via the dot operator, lambdas) work as decorator expressions.

## Applying multiple decorators

You can "stack" decorators:

```python
@dec1
@dec2
def foo():
  ...
```

Since a decorator gets the result of the lines below as an argument, this is equivalent to:

```python
def foo():
  ...
  
foo = dec1(dec2(foo))
```

So **the innermost/lowest decorator is applied first**, continuing outwards/up.

## Relationship to typing

Since [typing](./types.md) is limited in Starlark, compared to Python, it is currently not possible to preserve typing in the general case.
An identity decorator in Python 3.12 and up can statically indicate that it preserves the typing of the function that it has been given:

```python
def identity[T, **P](f: Callable[P, T]) -> Callable[P, T]:
    return f
```

Starlark does not support this syntax, so in these scenarios the type of decorated functions must be inferred (as `Any`).

```python
def identity(f):
    return f

@identity
def foo():
  pass
  
# type of foo is: Any
```
