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

//! A [Starlark interpreter in Rust](https://github.com/facebookexperimental/starlark-rust).
//! Starlark is a deterministic version of Python, with [a specification](https://github.com/bazelbuild/starlark/blob/master/spec.md),
//! used by (amongst others) the [Buck](https://buck.build) and [Bazel](https://bazel.build) systems.
//!
//! To evaluate a simple file:
//!
//! ```
//! # fn run() -> anyhow::Result<()> {
//! use starlark::eval::Evaluator;
//! use starlark::environment::{Module, Globals};
//! use starlark::values::Value;
//! use starlark::syntax::{AstModule, Dialect};
//!
//! let content = r#"
//! def hello():
//!    return "hello"
//! hello() + " world!"
//! "#;
//!
//! // We first parse the content, giving a filename and the Starlark
//! // `Dialect` we'd like to use (we pick standard).
//! let ast: AstModule = AstModule::parse("hello_world.star", content.to_owned(), &Dialect::Standard)?;
//!
//! // We create a `Globals`, defining the standard library functions available.
//! // By default, this uses those defined in the Starlark specification.
//! let globals: Globals = Globals::default();
//!
//! // We create a `Module`, which stores the global variables for our calculation.
//! let module: Module = Module::new();
//!
//! // We create an evaluator, which controls how evaluation occurs.
//! let mut eval: Evaluator = Evaluator::new(&module, &globals);
//!
//! // And finally we evaluate the code using the evaluator.
//! let res: Value = eval.eval_module(ast)?;
//! assert_eq!(res.unpack_str(), Some("hello world!"));
//! # Ok(())
//! # }
//! # fn main(){ run().unwrap(); }
//! ```

// Features we use
#![feature(backtrace)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(hash_set_entry)]
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

/// __macro_refs allows us to reference other crates in macro rules without users needing to be
///  aware of those dependencies. We make them public here and then can reference them like
///  `$crate::__macro_refs::foo`.
#[doc(hidden)]
pub mod __macro_refs {
    pub use paste;
}
