# Starlark in Rust

[![GitHub link](https://img.shields.io/badge/GitHub-facebookexperimental%2Fstarlark--rust-blue.svg)](https://github.com/facebookexperimental/starlark-rust)
[![crates.io version](https://img.shields.io/crates/v/starlark.svg)](https://crates.io/crates/starlark)
[![docs.rs availability](https://img.shields.io/docsrs/starlark?label=docs.rs)](https://docs.rs/starlark/)
[![Build status](https://img.shields.io/github/workflow/status/facebookexperimental/starlark-rust/ci.svg)](https://github.com/facebookexperimental/starlark-rust/actions)

_**NOTE:** Version 0.4.0 of this library changes maintainer from [Google](https://github.com/google/starlark-rust) to Facebook._

This project provides a Rust implementation of the [Starlark language](https://github.com/bazelbuild/starlark/blob/master/spec.md). Starlark (formerly codenamed Skylark) is a deterministic language inspired by Python3, used for configuration in the build systems [Bazel](https://bazel.build) and [Buck](https://buck.build). This project was originally developed [in this repo](https://github.com/google/starlark-rust), which contains a more extensive history.

There are at least three implementations of Starlark, [one in Java](https://github.com/bazelbuild/starlark), [one in Go](https://github.com/google/starlark-go), and this one in Rust. We mostly follow the Starlark standard.

## Features

This project features:

* Easy interoperability between Rust types and Starlark.
* Rust-friendly types, so frozen values are `Send`/`Sync`, while non-frozen values aren't.
* [Garbage collected](docs/gc.md) values allocated on [a heap](docs/heap.md).
* Optional runtime-checked [types](docs/types.md).
* A linter, to detect code issues in Starlark.
* IDE integration in the form of [LSP](https://microsoft.github.io/language-server-protocol/) and [DAP](https://microsoft.github.io/debug-adapter-protocol/) support.

This project also has three non-goals:

* We do _not_ aim for API stability between releases, preferring to iterate quickly and refine the API as much as possible. But we do [follow SemVer](https://doc.rust-lang.org/cargo/reference/semver.html).
* We do _not_ aim for minimal dependencies, preferring to keep one package with lots of power. But if some dependencies prove tricky, we might add feature flags.
* We do _not_ aim to work with Rust stable, preferring to take advantage of the unstable features in Rust to improve our code as much as possible. We hope that eventually enough features will be stabilised that using stable is reasonable again.

## Components

There are three components:

* `starlark_derive`, a proc-macro crate that defines the necessary macros for Starlark. This library is a dependency of `starlark` the library, which reexports all the relevant pieces, and should not be used directly.
* `starlark` the library, a library that defines the parser, evaluator and standard library. Projects wishing to embed Starlark in their environment (with additional types, library functions and features) will make use of this library.
* `starlark` the binary, which provides interactive evaluation, IDE features and linter, exposed through a command line. Useful if you want to use vanilla Starlark (but if you do, consider Python3 instead) or as a test-bed for experimenting. Most projects will end up implementing some of this functionality themselves over the `starlark` library, incorporating their specific extra types etc.

## Compatibility

In this section we outline where we don't comply with the [Starlark spec](https://github.com/bazelbuild/starlark/blob/master/spec.md).

* We have plenty of extensions, e.g. type annotations, recursion, top-level `for`.
* We don't yet support later additions to Starlark, such as [bytes](https://github.com/facebookexperimental/starlark-rust/issues/4).
* We are currently limited to [32 bit integers](https://github.com/facebookexperimental/starlark-rust/issues/6). Constructing larger values will result in Starlark failing with an overflow error.
* In some cases creating circular data structures may lead to stack overflows.

## Making a release

1. Check the [GitHub Actions](https://github.com/facebookexperimental/starlark-rust/actions) are green.
2. Update `CHANGELOG.md` with the changes since the last release. [This link](https://github.com/facebookexperimental/starlark-rust/compare/v0.4.0...main) can help (update to compare against the last release).
3. Update the version numbers of the two `Cargo.toml` files. Bump them by 0.0.1 if there are no incompatible changes, or 0.1.0 if there are. Bump the dependency in `starlark` to point at the latest `starlark_derive` version.
4. Copy the files `CHANGELOG.md`, `LICENSE` and `README.md` into each `starlark` and `starlark_derive` subdirectory.
5. Run `cargo publish --dry-run --allow-dirty`, then without the `--dry-run`, first in `starlark_derive` and then `starlark` directories.
6. Create a [GitHub release](https://github.com/facebookexperimental/starlark-rust/releases/new) with `v0.X.Y`, using the `starlark` version as the name.

## License

Starlark Rust is Apache License, Version 2.0 licensed, as found in the [LICENSE](LICENSE) file.
