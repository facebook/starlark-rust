# Starlark in Rust

This project provides a Rust implementation of the [Starlark language](https://github.com/bazelbuild/starlark/blob/master/spec.md). Starlark (formerly codenamed Skylark) is a deterministic language inspired by Python3, used for configuration in the build systems [Bazel](https://bazel.build) and [Buck](https://buck.build). This project was originally developed [in this repo](https://github.com/google/starlark-rust), which contains a more extensive history.

There are at least three implementations of Starlark, [one in Java](https://github.com/bazelbuild/starlark), [one in Go](https://github.com/google/starlark-go), and this one in Rust. We mostly follow the Starlark standard, but don't support most of the Go extensions (e.g. floating point numbers, bit operations, a set type).

## Features

This project features:

* Easy interoperability between Rust types and Starlark.
* Rust-friendly types, so frozen values are `Send`/`Sync`, which non-frozen values aren't.
* Garbage collected values allocated on a heap.
* Optional runtime-checked types.
* A linter, to detect code issues in Starlark.
* IDE integration in the form of [LSP](https://microsoft.github.io/language-server-protocol/) and [DAP](https://microsoft.github.io/debug-adapter-protocol/) support.

This project also has three non-goals:

* We do _not_ aim for API stability between releases, preferring to iterate quickly and refine the API as much as possible. But we do [follow SemVer](https://doc.rust-lang.org/cargo/reference/semver.html).
* We do _not_ aim for minimal dependencies, preferring to keep one package with lots of power. But if some dependencies prove tricky, we might add feature flags.
* We do _not_ aim to work with Rust stable, preferring to take advantage of the unstable features in Rust to improve our code as much as possible. We hope that eventually enough features will be stabilised that using stable is reasonable again.

## Components

There are three components:

* `starlark_module`, a proc-macro crate that defines the `#[starlark_module]` annotation that can be applied to Rust code to make it available as a Starlark module. This library is a dependency of `starlark` the library.
* `starlark` the library, a library that defines the parser, evaluator and standard library. Projects wishing to embed Starlark in their environment (with additional types, library functions and features) will make use of this library.
* `starlark` the binary, which provides interactive evaluation, IDE features and linter, exposed through a command line. Useful if you want to use vanilla Starlark (but if you do, consider Python3 instead) or as a test-bed for experimenting. Most projects will end up implementing some of this functionality themselves over the `starlark` library, incorporating their specific extra types etc.

## Compatibility

In this section we outline where we don't comply with the [Starlark spec](https://github.com/bazelbuild/starlark/blob/master/spec.md). Some of these incompatiblities are because we believe the Starlark spec could be improved - these are marked _deliberately_.

* We have plenty of extensions, e.g. type annotations, `lambda`, recursion.
* We don't have the common extensions of floats, bit operations, byte strings or sets.
* Our strings are not compliant in several ways, often returning code points instead of singleton strings, and have poor performance.
* Function arguments are sometimes evaluated in the wrong order, which is visible if their arguments have side effects.
* We follow proper lexical binding for list comprehensions, so each `for` clause introduces a fresh variable (_deliberately_).
* We allow comparison between `None` values (_deliberately_).
* In some cases creating circular data structures may lead to stack overflows.
* There are a number of minor incompatibilities or places where the spec is unclear, many of which are included in our tests.

## License

Starlark Rust is Apache License, Version 2.0 licensed, as found in the [LICENSE](LICENSE) file.
