/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

use crate::visitor::NodeKind;
use crate::visitor::VisitorImpl;
use crate::Allocative;
use crate::Key;
use crate::Visitor;

/// Size of data allocated in unique pointers in the struct.
///
/// * Exclude self
/// * Exclude shared pointers
/// * For unique pointers, include the size of the pointee plus this function recursively
pub fn size_of_unique_allocated_data(root: &dyn Allocative) -> usize {
    struct SizeOfUniqueAllocatedDataVisitor {
        /// Element added each time unique is entered,
        /// and element is incremented each time inline is entered.
        // TODO(nga): use smallvec.
        inlines_per_unique: Vec<u32>,
        /// Size we return.
        size: usize,
    }

    impl VisitorImpl for SizeOfUniqueAllocatedDataVisitor {
        fn enter_inline_impl<'a>(&'a mut self, _name: Key, size: usize) {
            if let Some(last) = self.inlines_per_unique.last_mut() {
                if *last == 0 {
                    self.size += size;
                }
                *last += 1;
            }
        }

        fn enter_unique_impl(&mut self, _name: Key, _size: usize) {
            self.inlines_per_unique.push(0);
        }

        fn enter_shared_impl(&mut self, _name: Key, _size: usize, _ptr: *const ()) -> bool {
            false
        }

        fn exit_inline_impl(&mut self) {
            if let Some(last) = self.inlines_per_unique.last_mut() {
                *last = last.checked_sub(1).unwrap();
            }
        }

        fn exit_unique_impl(&mut self) {
            let inlines = self.inlines_per_unique.pop().unwrap();
            assert_eq!(inlines, 0);
        }

        fn exit_shared_impl(&mut self) {
            unreachable!("shared pointers are not visited")
        }

        fn exit_root_impl(&mut self) {}
    }

    let mut visitor_impl = SizeOfUniqueAllocatedDataVisitor {
        size: 0,
        inlines_per_unique: Vec::new(),
    };
    let mut visitor = Visitor {
        visitor: &mut visitor_impl,
        node_kind: NodeKind::Root,
    };
    root.visit(&mut visitor);
    visitor.exit();
    visitor_impl.size
}

#[cfg(test)]
mod tests {
    use std::mem;

    use allocative_derive::Allocative;

    use crate as allocative;
    use crate::size_of_unique_allocated_data;

    #[test]
    fn test_box() {
        #[derive(Allocative)]
        struct Boxed {
            data: Box<u32>,
        }

        assert_eq!(
            mem::size_of::<u32>(),
            size_of_unique_allocated_data(&Boxed { data: Box::new(17) })
        );
    }

    #[test]
    fn test_box_slice() {
        #[derive(Allocative)]
        struct Boxed {
            data: Box<[u32]>,
        }

        assert_eq!(
            mem::size_of::<u32>() * 3,
            size_of_unique_allocated_data(&Boxed {
                data: vec![1, 2, 3].into_boxed_slice()
            })
        );
    }

    #[test]
    fn test_struct_in_box() {
        #[derive(Allocative)]
        struct Data {
            a: u8,
            b: Box<u32>,
        }

        #[derive(Allocative)]
        struct Boxed {
            data: Box<Data>,
        }

        assert_eq!(
            mem::size_of::<Data>() + mem::size_of::<u32>(),
            size_of_unique_allocated_data(&Boxed {
                data: Box::new(Data {
                    a: 1,
                    b: Box::new(2)
                })
            })
        );
    }
}
