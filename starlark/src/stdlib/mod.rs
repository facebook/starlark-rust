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

//! A module with the standard function and constants that are by default in all
//! dialect of Starlark

use crate::environment::GlobalsBuilder;

mod breakpoint;
pub(crate) mod dict;
pub(crate) mod enumeration;
mod extra;
mod funcs;
use gazebo::prelude::*;
pub(crate) mod list;
pub(crate) mod record;
pub(crate) mod string;
pub(crate) mod structs;
pub(crate) mod util;

/// Return the default global environment, it is not yet frozen so that a caller
/// can refine it.
///
/// For example `stdlib::standard_environment().freeze().child("test")` create a
/// child environment of this global environment that have been frozen.
pub(crate) fn standard_environment() -> GlobalsBuilder {
    GlobalsBuilder::new().with(funcs::global_functions)
}
#[derive(PartialEq, Eq, Copy, Clone, Dupe)]
pub enum LibraryExtension {
    StructType,
    RecordType,
    EnumType,
    Map,
    Filter,
    Partial,
    Dedupe,
    Debug,
    Print,
    Breakpoint,
    // Make sure if you add anything new, you add it to `all` below.
}

impl LibraryExtension {
    pub fn all() -> &'static [Self] {
        use LibraryExtension::*;
        &[
            StructType, RecordType, EnumType, Map, Filter, Partial, Dedupe, Debug, Print,
            Breakpoint,
        ]
    }

    pub fn add(self, builder: &mut GlobalsBuilder) {
        use LibraryExtension::*;
        match self {
            StructType => structs::global(builder),
            RecordType => record::global(builder),
            EnumType => enumeration::global(builder),
            Map => extra::map(builder),
            Filter => extra::filter(builder),
            Partial => extra::partial(builder),
            Dedupe => extra::dedupe(builder),
            Debug => extra::debug(builder),
            Print => extra::print(builder),
            Breakpoint => breakpoint::global(builder),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        self as starlark,
        assert::Assert,
        environment::{Globals, GlobalsBuilder, GlobalsStatic},
        values::{none::NoneType, Heap, StarlarkValue, UnpackValue, Value},
    };
    use gazebo::prelude::*;

    #[test]
    fn test_no_arg() {
        #[starlark_module]
        fn global(builder: &mut GlobalsBuilder) {
            fn nop() -> NoneType {
                Ok(NoneType)
            }
        }

        let env = GlobalsBuilder::new().with(global).build();
        env.get("nop").unwrap();
    }

    #[test]
    fn test_value_attributes() {
        #[derive(Copy, Clone, Debug, Dupe, PartialEq)]
        struct Bool2(bool);
        starlark_simple_value!(Bool2);

        impl<'v> StarlarkValue<'v> for Bool2 {
            starlark_type!("bool2");

            fn get_members(&self) -> Option<&'static Globals> {
                static RES: GlobalsStatic = GlobalsStatic::new();
                RES.members(members)
            }

            fn equals(&self, other: Value<'v>) -> anyhow::Result<bool> {
                match other.downcast_ref::<Bool2>() {
                    None => Ok(false),
                    Some(v) => Ok(*v == *self),
                }
            }
        }

        impl<'v> UnpackValue<'v> for Bool2 {
            fn unpack_value(value: Value<'v>, _heap: &'v Heap) -> Option<Self> {
                Some(*value.downcast_ref::<Bool2>().unwrap())
            }
        }

        #[starlark_module]
        fn globals(builder: &mut GlobalsBuilder) {
            const True2: Bool2 = Bool2(true);
            const False2: Bool2 = Bool2(false);
        }

        #[starlark_module]
        fn members(builder: &mut GlobalsBuilder) {
            #[attribute]
            fn invert1(x: Bool2) -> Bool2 {
                Ok(Bool2(!x.0))
            }

            fn invert2(x: Bool2) -> Bool2 {
                Ok(Bool2(!x.0))
            }
        }

        let mut a = Assert::new();
        a.globals_add(members);
        a.globals_add(globals);
        a.all_true(
            r#"
True2 == True2
True2 != False2
True2.invert1 == False2
False2.invert1 == True2
False2.invert2() == True2
hasattr(True2, "invert1") == True
hasattr(True2, "invert2") == True
hasattr(True2, "invert3") == False
dir(False2) == ["invert1","invert2"]
getattr(False2, "invert1") == True2
getattr(True2, "invert1") == False2
getattr(True2, "invert2")() == False2
"#,
        );
    }
}
