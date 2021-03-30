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

//! Module define the common engine error.

use crate::values::{StarlarkValue, Value};
use thiserror::Error;

/// Error that can be returned by function from the `StarlarkValue` trait,
#[derive(Debug, Error)]
pub enum ValueError {
    #[error("Operation `{op}` not supported on type `{typ}`")]
    OperationNotSupported { op: String, typ: String },
    #[error("Operation `{op}` not supported for types `{left}` and `{right}`")]
    OperationNotSupportedBinary {
        op: String,
        left: String,
        right: String,
    },
    #[error("Cannot divide by zero")]
    DivisionByZero,
    #[error("Integer overflow")]
    IntegerOverflow,
    #[error("Type of parameters mismatch")]
    IncorrectParameterType,
    #[error("Type of parameter `{0}` doesn't match")]
    IncorrectParameterTypeNamed(String),
    #[error("Index `{0}` is out of bound")]
    IndexOutOfBound(i32),
    #[error("Key `{0}` was not found")]
    KeyNotFound(String),
}

#[derive(Debug, Error)]
pub(crate) enum ControlError {
    #[error("Immutable")]
    CannotMutateImmutableValue,
    #[error("Value of type `{0}` is not hashable")]
    NotHashableValue(String),
    #[error("Too many recursion levels")]
    TooManyRecursionLevel,
    #[error("This operation mutate an iterable for an iterator while iterating.")]
    MutationDuringIteration,
}

pub(crate) fn unsupported_owned<T>(left: &str, op: &str, right: Option<&str>) -> anyhow::Result<T> {
    match right {
        None => Err(ValueError::OperationNotSupported {
            op: op.to_owned(),
            typ: left.to_owned(),
        }
        .into()),
        Some(right) => Err(ValueError::OperationNotSupportedBinary {
            op: op.to_owned(),
            left: left.to_owned(),
            right: right.to_owned(),
        }
        .into()),
    }
}

pub fn unsupported<'v, T, V: StarlarkValue<'v> + ?Sized>(left: &V, op: &str) -> anyhow::Result<T> {
    unsupported_owned(left.get_type(), op, None)
}

pub fn unsupported_with<'v, T, V: StarlarkValue<'v> + ?Sized>(
    left: &V,
    op: &str,
    right: Value,
) -> anyhow::Result<T> {
    unsupported_owned(left.get_type(), op, Some(right.get_type()))
}
