# starlark-rust and starlark in Meta

If something is missing here or outdated,
we appreciate if you submit a diff with the corrections.

## Projects using starlark-rust

When something changes in starlark-rust,
these projects may break.

* [buck2](https://www.internalfb.com/code/buck2)
  uses starlark as
  * a language for targets (`BUCK`, `TARGETS`)
    and macros and rules (`*.bzl`)
  * scripting language (BXL, `*.bxl`)
* antlir uses starlark to generate serialization code
  with shared definitions from bzl and python/rust
* metalos uses starlark to evaluate `HostConfig` generators
* netos (using it how?)
* codehub (using it how?)
* ai_productivity/promptlark
  [uses starlark in interative sessions](https://fburl.com/workplace/3um0vn1j)
* chronozl (cron jobs in fbcode described in starlark,
  [`*.chronos.bzl`](https://fburl.com/code/kzx3p477))
* flite (authoring ML features; where are the source files?)
* [JetBrains CLI](https://fburl.com/code/hetua4cx)
  (what it does with starlark?)

## Tools working with starlark-rust sources

When something changes in starlark-rust,
these tools may break.

* fork of Google's buildifier is used to
  [lint and format buck files](https://fburl.com/code/gnje3elg)
* [tools/build/buck/parser.py](https://fburl.com/code/w2j2nazt)
  starlark file parser written in Python, which parses `TARGETS` files
  by evaluating them, so modifications of starlark-rust
  break this parser
  * it is used by autodeps, which is a tooling to manage
    `TARGETS` files, in particular, manage deps
  * also used in [lionhead](https://fburl.com/code/sp6wv67n)
    to get a list of buck targets, and then generate new buck target
    that compile the same sources/dependencies with a different rule
    to obtain fuzz tests for the given code.
    Lionhead is part of product security.
    You can reach out to the oncall @dynamic_analysis for questions.

## Other starlark uses in Meta

* buck1 has a
  [starlark implementation in Java](https://www.internalfb.com/code/fbsource/xplat/build_infra/buck_client/starlark/)
  which is a fork of Bazel's starlark implementation.
* UTD and Skycastle define jobs using starlark (`*.td`, `*.sky`).
  They use a fork of buck1 fork of starlark.
