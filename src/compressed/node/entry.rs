use allocated::AllocResult;
use core::marker::PhantomData;
use core::ops::Add;
use core::ops::Mul;

extern crate alloc;
use alloc::vec::Vec;

use allocator_api2::alloc::Allocator;
use generic_array::ArrayLength;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use super::child_ptr::ChildPtr;
use super::node_ref::MutNodeRef;
use super::node_ref::NodeRefT;
use super::InsertOption;
use super::{InteriorNode, Node};

#[allow(clippy::module_name_repetitions)]
pub enum NodeEntry<
    's,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    Q: core::cmp::PartialOrd,
    V,
    B: ArrayLength,
    NR: NodeRefT<'s, K, V, B>,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
    // K: Borrow<Q>,
{
    Vacant(VacantNodeEntry<'s, K, Q, V, B, NR>),
    Occupied(OccupiedNodeEntry<'s, K, V, B, NR>),
}

#[allow(clippy::module_name_repetitions)]
pub struct VacantNodeEntry<
    's,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    Q: core::cmp::PartialOrd,
    V,
    B: ArrayLength,
    NR: NodeRefT<'s, K, V, B>,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
    // K: Borrow<Q>,
{
    key: Q,
    /// Path from root to the node, stored as (ancestor_node, child_index) pairs.
    /// The `usize` represents the child index at which we descended from that ancestor.
    /// This is used to determine whether we came from the left or right subtree when
    /// finding predecessor/successor keys.
    ancestors: Vec<(ChildPtr, usize)>,
    /// The node where the vacant entry would be inserted. Can be either a leaf or interior node.
    node: NR,
    i: usize,
    phantom: PhantomData<&'s Node<K, V, B>>,
}

#[allow(clippy::module_name_repetitions)]
pub struct OccupiedNodeEntry<
    's,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
    NR: NodeRefT<'s, K, V, B>,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Path from root to the node containing the occupied entry, stored as (ancestor_node, child_index) pairs.
    /// The `usize` represents the child index at which we descended from that ancestor.
    /// This is used during removal to propagate underflow corrections up the tree.
    ancestors: Vec<(ChildPtr, usize)>,
    node: NR,
    i: usize,
    phantom: PhantomData<&'s Node<K, V, B>>,
}

impl<
        's,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        Q: core::cmp::PartialOrd,
        V,
        B: ArrayLength,
        NR: NodeRefT<'s, K, V, B>,
    > VacantNodeEntry<'s, K, Q, V, B, NR>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
    // K: Borrow<Q>,
{
    pub(super) fn new(key: Q, ancestors: Vec<(ChildPtr, usize)>, node: NR, i: usize) -> Self {
        Self {
            key,
            ancestors,
            node,
            i,
            phantom: PhantomData,
        }
    }

    pub fn key(&self) -> &Q {
        &self.key
    }

    pub fn into_key(self) -> Q {
        self.key
    }

    /// Returns a reference to the key that would be immediately below (predecessor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the minimum key.
    pub fn key_below(&self) -> Option<&K>
    where
        K: core::cmp::PartialOrd,
    {
        // Check if we can get predecessor from current node
        if self.i > 0 {
            return Some(self.node.key_at(self.i - 1));
        }

        // Walk up ancestors to find predecessor
        for (ancestor_ptr, ancestor_i) in self.ancestors.iter().rev() {
            if *ancestor_i > 0 {
                // We came from the right at this ancestor, so predecessor is at ancestor_i - 1
                // SAFETY: The ancestor ChildPtr was stored during tree traversal and points
                // to a valid node in the tree with lifetime 's (the same as self).
                // The index ancestor_i - 1 is valid because ancestor_i > 0.
                return Some(unsafe { ancestor_ptr.get_key_at::<K, V, B>(ancestor_i - 1) });
            }
        }

        // No predecessor found - this would be the minimum key
        None
    }

    /// Returns a reference to the key that would be immediately above (successor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the maximum key.
    pub fn key_above(&self) -> Option<&K>
    where
        K: core::cmp::PartialOrd,
    {
        // Check if we can get successor from current node
        let n_keys = self.node.n_keys();
        if self.i < n_keys {
            return Some(self.node.key_at(self.i));
        }

        // Walk up ancestors to find successor
        for (ancestor_ptr, ancestor_i) in self.ancestors.iter().rev() {
            // Check if there's a key at ancestor_i (meaning we came from the left)
            // We need to check n_keys first to ensure ancestor_i is valid
            let n_keys = ancestor_ptr.as_node_ref::<K, V, B>().n_keys();
            if *ancestor_i < n_keys {
                // We came from the left at this ancestor, so successor is at ancestor_i
                // SAFETY: The ancestor ChildPtr was stored during tree traversal and points
                // to a valid node in the tree with lifetime 's (the same as self).
                // The index ancestor_i is valid because ancestor_i < n_keys.
                return Some(unsafe { ancestor_ptr.get_key_at::<K, V, B>(*ancestor_i) });
            }
        }

        // No successor found - this would be the maximum key
        None
    }
}

impl<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
    VacantNodeEntry<'s, K, K, V, B, MutNodeRef<'s, K, V, B>>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn insert_in<'a, A: Allocator>(
        self,
        alloc: &'a A,
        value: V,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let mut key = self.key;
        let mut value = value;
        let mut rhn = None;

        // First, try to insert into the node
        // SAFETY: Caller ensures alloc matches the allocator used for this tree
        let r = unsafe { self.node.insert_in_here(alloc, key, value, self.i, rhn)? };
        match r {
            InsertOption::NewKey(v) => {
                return Ok(InsertOption::NewKey(v));
            }
            InsertOption::Split((k, v, new_rhn)) => {
                key = k;
                value = v;
                rhn = Some(new_rhn);
            }
        }

        // If we split, propagate up through ancestors
        for (ancestor_ptr, i) in self.ancestors.into_iter().rev() {
            let node = ancestor_ptr.as_mut_node_ref();
            // Use `i` directly - the child index we descended through equals
            // the key index where the median should be inserted
            // SAFETY: Caller ensures alloc matches the allocator used for this tree
            let r = unsafe { node.insert_in_here(alloc, key, value, i, rhn)? };
            match r {
                InsertOption::NewKey(v) => {
                    return Ok(InsertOption::NewKey(v));
                }
                InsertOption::Split((k, v, new_rhn)) => {
                    key = k;
                    value = v;
                    rhn = Some(new_rhn);
                }
            }
        }

        Ok(InsertOption::Split((key, value, rhn.unwrap())))
    }
}

impl<
        's,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
        NR: NodeRefT<'s, K, V, B>,
    > OccupiedNodeEntry<'s, K, V, B, NR>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
    // K: Borrow<Q>,
{
    pub(super) fn new(ancestors: Vec<(ChildPtr, usize)>, node: NR, i: usize) -> Self {
        Self {
            ancestors,
            node,
            i,
            phantom: PhantomData,
        }
    }

    pub fn key(&self) -> &K {
        // &self.key
        self.node.key_at(self.i)
    }

    pub fn get(&self) -> &V {
        self.node.value_at(self.i)
    }

    pub fn into_value(self) -> &'s V {
        self.node.into_value_at(self.i)
    }

    pub fn into_key_value(self) -> (&'s K, NR::ValueRef) {
        self.node.into_key_value_at(self.i)
    }
}

impl<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
    OccupiedNodeEntry<'s, K, V, B, MutNodeRef<'s, K, V, B>>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn get_mut(&mut self) -> &mut V {
        self.node.value_at_mut(self.i)
    }

    pub fn into_mut(self) -> &'s mut V {
        self.node.into_value_at_mut(self.i)
    }

    pub fn insert(&mut self, mut value: V) -> V {
        core::mem::swap(&mut value, self.node.value_at_mut(self.i));
        value
    }

    /// # Safety
    ///
    /// `alloc` must be the allocator used to allocate children in this node.
    pub unsafe fn remove<A: Allocator>(mut self, alloc: &A) -> ((K, V), bool) {
        // SAFETY: Caller ensures alloc matches the allocator used for this tree
        unsafe {
            let r = self.node.remove_from_here_in(alloc, self.i);

            for (parent, j) in self.ancestors.iter().rev().copied() {
                let parent: &mut InteriorNode<K, V, B> =
                    parent.as_mut_node_ref().into_interior_node();
                if !parent.check_underflow(alloc, j) {
                    return (r, false);
                }
            }

            (r, true)
        }
    }
}
