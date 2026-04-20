/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is dual-licensed under either the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree or the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree. You may select, at your option, one of the
 * above-listed licenses.
 */

//! Pagable-native trait object serialization using inventory for auto-registration.
//!
//! This module provides a trait object serialization system similar to `typetag`,
//! but using PagableSerialize/PagableBoxDeserialize instead of serde traits.
//!
//! It uses the `inventory` crate for automatic registration of concrete types
//! at program startup, so there's no need for explicit registration calls.
//!
//! # Usage
//!
//! Use the `#[pagable_typetag]` attribute on both the trait definition and
//! each impl block:
//!
//! ```ignore
//! #[pagable::pagable_typetag]
//! trait MyTrait: pagable::typetag::PagableTagged + Send + Sync {
//!     fn do_something(&self);
//! }
//!
//! #[derive(pagable::Pagable)]
//! struct MyImpl { value: i32 }
//!
//! #[pagable::pagable_typetag]
//! impl MyTrait for MyImpl {
//!     fn do_something(&self) { println!("{}", self.value); }
//! }
//! ```
//!
//! # How it works
//!
//! The `#[pagable_typetag]` attribute macro on a trait definition generates:
//! - A trait-specific registration struct
//! - A static registry to collect registered implementations
//! - `inventory::collect!` for the registration struct
//! - `PagableSerialize` impl for `dyn Trait`
//! - `PagableBoxDeserialize` impl for `dyn Trait`
//!
//! The `#[pagable_typetag]` attribute macro on an impl block generates:
//! - `PagableTagged` impl for the concrete type (using the type name as the tag)
//! - `inventory::submit!` to register the type with its tag

use std::collections::HashMap;

use crate::PagableDeserializer;
use crate::PagableSerialize;
use crate::PagableSerializer;

/// Object-safe serialization trait for tagged types.
///
/// This trait is dyn-compatible and used by trait objects to serialize
/// themselves with a type tag.
pub trait PagableTagged: PagableSerialize + Send + Sync {
    /// Get the type tag for this concrete type.
    fn pagable_type_tag(&self) -> &'static str;

    fn serialize_tagged(&self, serializer: &mut dyn PagableSerializer) -> crate::Result<()> {
        let tag = self.pagable_type_tag();
        serde::Serialize::serialize(&tag, serializer.serde())?;
        self.pagable_serialize(serializer)
    }
}

/// Marker trait: implemented for inner types registered via `register_typetag!`
/// for a specific `(Trait, Wrapper<Inner>)` triple. Use as a bound to enforce
/// registration at compile time.
///
/// The second type parameter names the wrapper a given inner type is registered
/// for, which lets the same inner type be registered under multiple wrappers
/// against the same trait without conflicting impls.
///
/// ```ignore
/// #[pagable_tagged(MyTrait)]
/// struct Wrapper<T: MyInnerTrait>(pub T)
/// where
///     T: PagableRegisteredFor<dyn MyTrait, Wrapper<T>>;
/// ```
pub trait PagableRegisteredFor<T: ?Sized, W: ?Sized> {}

/// Registration entry for a concrete type implementing a trait object.
///
/// Used by both `#[pagable_typetag]` (proc macro) and `register_typetag!` (macro_rules).
pub struct TypetagRegistration<T: ?Sized + 'static> {
    pub tag: fn() -> &'static str,
    pub deserialize: fn(&mut dyn PagableDeserializer<'_>) -> crate::Result<Box<T>>,
}

// SAFETY: TypetagRegistration only contains function pointers (fn types),
// which are inherently Send + Sync.
unsafe impl<T: ?Sized> Send for TypetagRegistration<T> {}
unsafe impl<T: ?Sized> Sync for TypetagRegistration<T> {}

/// A registry built from `TypetagRegistration` entries collected via `inventory`.
pub struct TypetagRegistry<T: ?Sized + 'static> {
    map: HashMap<&'static str, fn(&mut dyn PagableDeserializer<'_>) -> crate::Result<Box<T>>>,
}

impl<T: ?Sized + 'static> TypetagRegistry<T> {
    pub fn from_inventory(iter: impl Iterator<Item = &'static TypetagRegistration<T>>) -> Self {
        let mut map = HashMap::new();
        for reg in iter {
            map.insert((reg.tag)(), reg.deserialize);
        }
        TypetagRegistry { map }
    }

    pub fn deserialize_tagged(
        &self,
        deserializer: &mut dyn PagableDeserializer<'_>,
    ) -> crate::Result<Box<T>> {
        let tag: String = serde::Deserialize::deserialize(deserializer.serde())?;
        let deserialize_fn = self
            .map
            .get(tag.as_str())
            .ok_or_else(|| crate::__internal::anyhow::anyhow!("Unknown type tag: {}", tag))?;
        (deserialize_fn)(deserializer)
    }
}

/// Register a concrete generic instantiation for pagable deserialization.
///
/// Use for generic wrappers where `#[pagable_typetag]` can't be applied.
/// Implements `PagableRegisteredFor` for the inner type and registers
/// `Wrapper<Inner>` for deserialization.
///
/// The trait must have `#[pagable_typetag]` applied.
///
/// # Example
///
/// ```ignore
/// pagable::register_typetag!(Wrapper<Cat> as dyn MyTrait);
/// ```
#[macro_export]
macro_rules! register_typetag {
    ($wrapper:ident < $inner:ty > as dyn $trait:path) => {
        impl $crate::typetag::PagableRegisteredFor<dyn $trait, $wrapper<$inner>> for $inner {}

        $crate::__internal::inventory::submit! {
            <dyn $trait>::__pagable_wrap_registration(
                $crate::typetag::TypetagRegistration {
                    tag: ::std::any::type_name::<$wrapper<$inner>>,
                    deserialize: |deserializer| {
                        let value: $wrapper<$inner> =
                            $crate::PagableDeserialize::pagable_deserialize(deserializer)?;
                        Ok(Box::new(value) as Box<dyn $trait>)
                    },
                }
            )
        }
    };
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;
    use std::sync::Arc;

    use pagable::PagableRegisteredFor;
    use pagable::PagableTagged;

    use crate as pagable;
    use crate::Pagable;

    #[crate::pagable_typetag]
    pub trait Named: PagableTagged + Send + Sync + Debug {
        fn name(&self) -> &str;
    }

    #[derive(Pagable, Debug, Eq, PartialEq)]
    pub struct Key {
        pub name: Arc<String>,
    }

    #[crate::pagable_typetag]
    impl Named for Key {
        fn name(&self) -> &str {
            &self.name
        }
    }

    #[derive(Pagable, Debug, Eq, PartialEq)]
    #[crate::pagable_typetag(Named)]
    pub struct Bar {
        pub name: Arc<String>,
    }

    pub trait NamedDyn: PagableTagged + Send + Sync + Debug {
        fn name(&self) -> &str;
    }

    impl NamedDyn for Bar {
        fn name(&self) -> &str {
            &self.name
        }
    }

    impl<T: NamedDyn> Named for T {
        fn name(&self) -> &str {
            NamedDyn::name(self)
        }
    }

    #[test]
    fn test_typetag_roundtrip() -> crate::Result<()> {
        use crate::testing::TestingDeserializer;
        use crate::testing::TestingSerializer;
        use crate::traits::PagableBoxDeserialize;

        let value: Arc<dyn Named> = Arc::new(Key {
            name: Arc::new("test".to_owned()),
        });

        let mut serializer = TestingSerializer::new();
        value.serialize_tagged(&mut serializer)?;
        let bytes = serializer.finish();

        let mut deserializer = TestingDeserializer::new(&bytes);

        let restored: Box<dyn Named> = <dyn Named>::deserialize_box(&mut deserializer)?;

        assert_eq!(restored.name(), "test");
        Ok(())
    }

    // --- Generic wrapper tests (like TyCustomFunction<F>) ---
    // Uses register_typetag! + TypetagRegistry instead of #[pagable_typetag]

    /// Trait for the dyn object (like TyCustomDyn)
    #[crate::pagable_typetag]
    pub trait Animal: PagableTagged + Send + Sync + Debug {
        fn species(&self) -> &str;
    }

    /// Generic wrapper (like TyCustomFunction<F>).
    /// The Registered bound on T enforces that only registered inner types can be used.
    #[derive(Debug, Pagable)]
    #[crate::pagable_tagged(Animal)]
    pub struct Wrapper<T: Pagable + Send + Sync + Debug + 'static>(pub T);

    impl<T: Pagable + Send + Sync + Debug + 'static> Animal for Wrapper<T>
    where
        T: PagableRegisteredFor<dyn Animal, Self>,
    {
        fn species(&self) -> &str {
            "wrapped"
        }
    }

    /// Concrete inner type (like ZipType) — registered
    #[derive(Debug, Pagable, Eq, PartialEq)]
    pub struct Cat;

    // Register Wrapper<Cat> for deserialization as dyn Animal.
    // This generates: impl PagableRegisteredFor<dyn Animal, Wrapper<Cat>> for Cat {}
    crate::register_typetag!(Wrapper<Cat> as dyn Animal);

    #[test]
    fn test_register_typetag_generic_roundtrip() -> crate::Result<()> {
        use crate::testing::TestingDeserializer;
        use crate::testing::TestingSerializer;
        use crate::traits::PagableBoxDeserialize;

        let value: Arc<dyn Animal> = Arc::new(Wrapper(Cat));

        let mut serializer = TestingSerializer::new();
        value.serialize_tagged(&mut serializer)?;
        let bytes = serializer.finish();

        let mut deserializer = TestingDeserializer::new(&bytes);
        let restored: Box<dyn Animal> = <dyn Animal>::deserialize_box(&mut deserializer)?;

        assert_eq!(restored.species(), "wrapped");
        Ok(())
    }

    // Using an unregistered type as `dyn Animal` fails to compile:
    // #[derive(Debug, Pagable)]
    // struct Dog;
    // const _: Arc<dyn Animal> = Arc::new(Wrapper(Dog));
    //      error: Dog: PagableRegisteredFor<dyn Animal, Wrapper<Dog>> is not satisfied

    #[test]
    fn test_typetag_roundtrip_indirect_impl() -> crate::Result<()> {
        use crate::testing::TestingDeserializer;
        use crate::testing::TestingSerializer;
        use crate::traits::PagableBoxDeserialize;

        let value: Arc<dyn Named> = Arc::new(Bar {
            name: Arc::new("test".to_owned()),
        });

        let mut serializer = TestingSerializer::new();
        value.serialize_tagged(&mut serializer)?;
        let bytes = serializer.finish();

        let mut deserializer = TestingDeserializer::new(&bytes);

        let restored: Box<dyn Named> = <dyn Named>::deserialize_box(&mut deserializer)?;

        assert_eq!(restored.name(), "test");
        Ok(())
    }
}
