use allocator_api2::alloc::Allocator;
use core::marker::PhantomData;
use core::ops::Add;
use core::ops::Mul;

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;

use generic_array::ArrayLength;

use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use super::{Node, NodeRef};

pub struct Iter<
    'a,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
    NR: NodeRef<'a, K, V, B>,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    stack: Vec<(NR::Ptr, usize)>,
    phantom: PhantomData<&'a Node<K, V, B>>,
}

impl<
        'a,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
        NR: NodeRef<'a, K, V, B>,
    > Iter<'a, K, V, B, NR>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(crate) fn new(stack: Vec<(NR::Ptr, usize)>) -> Self {
        Self {
            stack,
            phantom: PhantomData,
        }
    }
}

impl<
        'a,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
        NR: NodeRef<'a, K, V, B>,
    > Iterator for Iter<'a, K, V, B, NR>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = (&'a K, NR::ValueRef);

    fn next(&mut self) -> Option<Self::Item> {
        let mut e = self.stack.pop();
        while let Some((node, i)) = e {
            // SAFETY: Requires node is a valid pointer with appropriate lifetime
            let mut node: NR = unsafe { NR::from_ptr(node) };
            if i == node.n_keys + 1 {
                e = self.stack.pop();
                while let Some((node, i)) = e {
                    // SAFETY: Requires node is a valid pointer with appropriate lifetime
                    let mut node: NR = unsafe { NR::from_ptr(node) };
                    if i == node.n_keys + 1 {
                        e = self.stack.pop();
                    } else {
                        self.stack.push((node.as_ptr(), i));

                        return Some(node.into_key_value_at(i - 1));
                    }
                }

                return None;
            } else if node.is_leaf() {
                if i == node.n_keys {
                    e = Some((node.as_ptr(), i + 1));
                    continue;
                }

                self.stack.push((node.as_ptr(), i + 1));
                return Some(node.into_key_value_at(i));
            }

            self.stack.push((node.as_ptr(), i + 1));

            let child = node.child_at(i).unwrap();
            // SAFETY: Requires child is a valid node pointer with appropriate lifetime
            e = Some((unsafe { NR::from_non_null(*child) }.as_ptr(), 0));
        }

        None
    }
}

pub struct IntoIter<
    'a,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
    A: Allocator,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    alloc: &'a A,
    stack: Vec<(Node<K, V, B>, usize)>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: Allocator>
    IntoIter<'a, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(crate) fn new(alloc: &'a A, root: Node<K, V, B>) -> Self {
        Self {
            alloc,
            stack: vec![(root, 0)],
        }
    }
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: Allocator> Iterator
    for IntoIter<'a, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let mut e = self.stack.pop();
        while let Some((mut node, i)) = e {
            if i == node.n_keys + 1 {
                e = self.stack.pop();
                while let Some((mut node, i)) = e {
                    if i == node.n_keys + 1 {
                        e = self.stack.pop();
                    } else {
                        let r = node.take_key_value_at(i - 1);
                        self.stack.push((node, i));

                        return Some(r);
                    }
                }

                return None;
            } else if node.is_leaf() {
                if i == node.n_keys {
                    e = Some((node, i + 1));
                    continue;
                }

                let child = node.take_key_value_at(i);
                self.stack.push((node, i + 1));
                return Some(child);
            }

            let child = node.take_child_at_in(self.alloc, i);
            self.stack.push((node, i + 1));
            e = Some((child, 0));
        }

        None
    }
}
