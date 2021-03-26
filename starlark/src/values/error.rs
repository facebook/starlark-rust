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
#[derive(Clone, Debug, Error)]
// FIXME: Would be good if this wasn't public, or only a subset of constructors were public.
pub enum ValueError {
    /// The operation is not supported for this type.
    #[error("Operation `{op}` not supported on type `{typ}`")]
    OperationNotSupported { op: String, typ: String },
    /// The operation is not supported for this type.
    #[error("Operation `{op}` not supported for types `{left}` and `{right}`")]
    OperationNotSupportedBinary {
        op: String,
        left: String,
        right: String,
    },
    /// Division by 0
    #[error("Cannot divide by zero")]
    DivisionByZero,
    /// Arithmetic operation results in integer overflow.
    #[error("Integer overflow")]
    IntegerOverflow,
    /// Trying to modify an immutable value.
    #[error("Immutable")]
    CannotMutateImmutableValue,
    /// Trying to apply incorrect parameter type, e.g. for slicing.
    #[error("Type of parameters mismatch")]
    IncorrectParameterType,
    /// Trying to apply incorrect parameter type, e.g. for slicing.
    #[error("Type of parameter `{0}` doesn't match")]
    IncorrectParameterTypeNamed(String),
    /// Trying to access an index outside of the value range,
    #[error("Index `{0}` is out of bound")]
    IndexOutOfBound(i32),
    /// The value is not hashable but was requested for a hash structure (e.g.
    /// dictionary).
    #[error("Value of type `{0}` is not hashable")]
    NotHashableValue(String),
    /// The key was not found in the collection, stores the repr of the value.
    #[error("Key `{0}` was not found")]
    KeyNotFound(String),
    /// Too many recursion in internal operation
    #[error("Too many recursion levels")]
    TooManyRecursionLevel,
    /// It is not allowed to mutate a structure during iteration.
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
