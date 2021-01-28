/*
 * Copyright 2018 The Starlark in Rust Authors.
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

//! A Starlark interpreter library in rust.
//!
//! Starlark, formerly codenamed Skylark, is a non-Turing complete language
//! based on Python that was made for the [Bazel build system](https://bazel.build) to define compilation plugin.
//!
//! Starlark has at least 3 implementations: a [Java one for Bazel](
//! https://github.com/bazelbuild/bazel/tree/master/src/main/java/com/google/devtools/skylark),
//! a [go one](https://github.com/google/skylark) and this one.
//!
//! This interpreter was made using the [specification from the go version](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
//! and the Python 3 documentation when things were unclear.
//!
//! This interpreter does not support most of the go extensions (e.g. bitwise
//! operator or floating point). It does not include the `set()` type either
//! (the Java implementation use a custom type, `depset`, instead). It uses
//! signed 64-bit integer.
//!
//! # Usage
//!
//! The library can be used to define a dialect of Starlark (e.g. for a build
//! system).
//!
//! The methods in the [eval](eval) modules can be used to evaluate Starlark
//! code:
//!   * General purpose [eval](eval::eval_module) and function evaluate Starlark code
//!     and return the result of the last statement. Those are generic purpose
//!     function to be used when rewiring load statements.
//!   * A file loader that simply load relative path to the program is provided
//!     by the simple module. This module also contains version of eval and
//!     eval_file that use this file loader.
//!   * Interactive versions of those function are provided in the interactive
//!     module. Those function are printing the result / diagnostic to the
//!     stdout / stderr instead of returning an output.
//!
//! # Defining a Starlark dialect
//!
//! To specify a new Starlark dialect, the global Environment can be
//! edited, adding functions or constants. The
//! [starlark_module](macro@starlark_module) macro let you define new function with
//! limited boilerplate.
//!
//! Those added function or macros can however return their own type, all of
//! them should implement the [TypedValue](values::TypedValue) trait. See the
//! documentation of the [values](values) module.
//!
//! # Content of the default global environment
//!
//! The default global environment is returned by the
//! [stdlib::standard_environment] function and add the `True`,
//! `False` and `None` constants, as well as the functions in the [stdlib]
//! module.
//!
//! # Provided types
//!
//! The [values](values) module provide the following types:
//!
//! * integer (signed 64bit), bool, and NoneType,
//! * [string](values::string),
//! * [dictionary](values::dict),
//! * [list](values::list),
//! * [tuple](values::tuple), and
//! * [function](values::function).

// Features we use
#![feature(backtrace)]
#![feature(box_syntax)]
#![feature(hash_set_entry)]
#![feature(iter_order_by)]
#![feature(trait_alias)]
#![feature(try_blocks)]
//
// Plugins
#![cfg_attr(feature = "custom_linter", feature(plugin))]
#![cfg_attr(feature = "custom_linter", allow(deprecated))] // :(
#![cfg_attr(feature = "custom_linter", plugin(linter))]
//
// Good reasons
#![allow(clippy::new_ret_no_self)] // We often return Value, even though its morally a Self
#![allow(clippy::needless_return)] // Mixing explicit returns with implicit ones sometimes looks odd
// Disagree these are good hints
#![allow(clippy::single_match)]
#![allow(clippy::should_implement_trait)]
#![allow(clippy::len_without_is_empty)]
#![allow(clippy::match_like_matches_macro)]
#![allow(clippy::new_without_default)]
#![allow(clippy::type_complexity)]
#![allow(clippy::needless_lifetimes)]
// FIXME: Temporary
#![allow(clippy::useless_transmute)] // Seems to be a clippy bug, but we should be using less transmute anyway
#![allow(clippy::boxed_local)] // Should remove some boxes
#![allow(clippy::vec_box)] // Should remove some boxes
#![allow(clippy::borrowed_box)] // Should remove some boxes

#[macro_use]
extern crate gazebo;
#[macro_use]
extern crate starlark_module;
#[macro_use]
extern crate maplit;

#[macro_use]
mod macros;

pub mod analysis;
pub mod assert;
pub mod collections;
pub mod debug;
pub mod environment;
pub mod errors;
pub mod eval;
pub mod stdlib;
pub mod syntax;
pub mod values;
