/*
 * Copyright 2021 The Starlark in Rust Authors.
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

//! Helpers for numerical values.

use super::Value;

#[derive(Clone, Copy, Debug)]
pub enum Num {
    Int(i32),
    Float(f64),
}


impl Num {
    pub fn try_from_value(value: Value) -> Option<Self> {
        if let Some(i) = value.unpack_int() {
            Some(Self::Int(i))
        } else if let Some(&f) = value.get_ref().downcast_ref::<f64>() {
            Some(Self::Float(f))
        } else {
            None
        }
    }

    pub fn is_int(self) -> bool {
        match self {
            Self::Int(_) => true,
            Self::Float(_) => false,
        }
    }

    pub fn is_float(self) -> bool {
        match self {
            Self::Int(_) => false,
            Self::Float(_) => true,
        }
    }

    pub fn as_float(self) -> f64 {
        match self {
            Self::Int(i) => i as f64,
            Self::Float(f) => f,
        }
    }

    pub fn as_int(self) -> Option<i32> {
        match self {
            Self::Int(i) => Some(i),
            Self::Float(f) => {
                let int_candidate = f.trunc();
                if f == int_candidate && int_candidate <= i32::MAX as f64 && int_candidate >= i32::MIN as f64 {
                    Some(f as i32)
                } else {
                    // Has fractional part or out of bounds -> not in range.
                    None
                }
            }
        }
    }
}

impl From<i32> for Num {
    fn from(i: i32) -> Self {
        Self::Int(i)
    }
}

impl From<f64> for Num {
    fn from(f: f64) -> Self {
        Self::Float(f)
    }
}
