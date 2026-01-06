use allocated::AllocResult;
use core::fmt::Debug;
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

use super::InsertOption;
use super::Node;
use super::NodeRef;

#[allow(clippy::module_name_repetitions)]
pub enum NodeEntry<
    's,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    Q: core::cmp::PartialOrd,
    V,
    B: ArrayLength,
    NR: NodeRef<'s, K, V, B>,
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
    NR: NodeRef<'s, K, V, B>,
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
    ancestors: Vec<(NR::Ptr, usize)>,
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
    NR: NodeRef<'s, K, V, B>,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Path from root to the node containing the occupied entry, stored as (ancestor_node, child_index) pairs.
    /// The `usize` represents the child index at which we descended from that ancestor.
    /// This is used during removal to propagate underflow corrections up the tree.
    ancestors: Vec<(NR::Ptr, usize)>,
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
        NR: NodeRef<'s, K, V, B>,
    > VacantNodeEntry<'s, K, Q, V, B, NR>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
    // K: Borrow<Q>,
{
    pub(super) fn new(key: Q, ancestors: Vec<(NR::Ptr, usize)>, node: NR, i: usize) -> Self
    where
        Q: Debug,
    {
        // println!("VacantNode key={:?}", key);

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
}

impl<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
    VacantNodeEntry<'s, K, K, V, B, &'s mut Node<K, V, B>>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Returns a reference to the node and index of the entry immediately below (predecessor of)
    /// this vacant entry. Returns `None` if the vacant entry would be the minimum key.
    fn index_below(&self) -> Option<(&Node<K, V, B>, usize)> {
        // Check if predecessor is in current node
        if self.i > 0 {
            return Some((&*self.node, self.i - 1));
        }

        // Walk up ancestors to find predecessor
        for (ancestor_ptr, ancestor_i) in self.ancestors.iter().rev().copied() {
            if ancestor_i > 0 {
                // We came from the right at this ancestor, so predecessor is at ancestor_i - 1
                // SAFETY: The ancestor pointer was stored during tree traversal and points
                // to a valid node in the tree with the same lifetime as self.
                let ancestor = unsafe { &*ancestor_ptr };
                return Some((ancestor, ancestor_i - 1));
            }
        }

        // No predecessor found - this would be the minimum key
        None
    }

    /// Returns a reference to the node and index of the entry immediately above (successor of)
    /// this vacant entry. Returns `None` if the vacant entry would be the maximum key.
    fn index_above(&self) -> Option<(&Node<K, V, B>, usize)> {
        // Check if successor is in current node
        if self.i < self.node.n_keys() {
            return Some((&*self.node, self.i));
        }

        // Walk up ancestors to find successor
        for (ancestor_ptr, ancestor_i) in self.ancestors.iter().rev().copied() {
            // SAFETY: The ancestor pointer was stored during tree traversal and points
            // to a valid node in the tree with the same lifetime as self.
            let ancestor = unsafe { &*ancestor_ptr };
            if ancestor_i < ancestor.n_keys() {
                // We came from the left at this ancestor, so successor is at ancestor_i
                return Some((ancestor, ancestor_i));
            }
        }

        // No successor found - this would be the maximum key
        None
    }

    /// Returns a reference to the key that would be immediately below (predecessor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the minimum key.
    pub fn key_below(&self) -> Option<&K> {
        let (node, i) = self.index_below()?;
        Some(node.key_at(i))
    }

    /// Returns a reference to the key that would be immediately above (successor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the maximum key.
    pub fn key_above(&self) -> Option<&K> {
        let (node, i) = self.index_above()?;
        Some(node.key_at(i))
    }

    /// Returns a reference to the value that would be immediately below (predecessor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the minimum key.
    #[must_use]
    pub fn value_below(&self) -> Option<&V> {
        let (node, i) = self.index_below()?;
        Some(node.value_at(i))
    }

    /// Returns a reference to the value that would be immediately above (successor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the maximum key.
    #[must_use]
    pub fn value_above(&self) -> Option<&V> {
        let (node, i) = self.index_above()?;
        Some(node.value_at(i))
    }

    /// Returns a reference to the key-value pair that would be immediately below (predecessor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the minimum key.
    #[must_use]
    pub fn below(&self) -> Option<(&K, &V)> {
        let (node, i) = self.index_below()?;
        Some((node.key_at(i), node.value_at(i)))
    }

    /// Returns a reference to the key-value pair that would be immediately above (successor of)
    /// the vacant entry's key in the tree's sorted order.
    /// Returns `None` if the vacant entry would be the maximum key.
    #[must_use]
    pub fn above(&self) -> Option<(&K, &V)> {
        let (node, i) = self.index_above()?;
        Some((node.key_at(i), node.value_at(i)))
    }

    /// Inserts a value into the vacant entry.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `alloc` is the same allocator instance used
    /// to construct the B-tree. Using a different allocator will result in
    /// undefined behavior.
    pub unsafe fn insert_in<'a, A: Allocator>(
        self,
        alloc: &'a A,
        value: V,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let mut key = self.key;
        let mut value = value;
        let mut rhn = None;

        // First, try to insert into the node
        // SAFETY: `alloc` is the same allocator used to create the B-tree (caller requirement).
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
            // SAFETY: The ancestor pointer was stored during tree traversal and is valid
            // for the lifetime 's. We have exclusive access through the entry.
            let node = unsafe { &mut *ancestor_ptr };
            // Use `i` directly - the child index we descended through equals
            // the key index where the median should be inserted
            // SAFETY: `alloc` is the same allocator used to create the B-tree (caller requirement).
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
        NR: NodeRef<'s, K, V, B>,
    > OccupiedNodeEntry<'s, K, V, B, NR>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
    // K: Borrow<Q>,
{
    pub(super) fn new(ancestors: Vec<(NR::Ptr, usize)>, node: NR, i: usize) -> Self {
        // println!("OccupiedNodeEntry node={:?} i={:?}", node, i);

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
    OccupiedNodeEntry<'s, K, V, B, &'s mut Node<K, V, B>>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Returns a reference to the node and index of the entry immediately below (predecessor of)
    /// this occupied entry. Returns `None` if this entry is the minimum key.
    fn index_below(&self) -> Option<(&Node<K, V, B>, usize)> {
        // Check if predecessor is in current node
        if self.i > 0 {
            return Some((&*self.node, self.i - 1));
        }

        // Walk up ancestors to find predecessor
        for (ancestor_ptr, ancestor_i) in self.ancestors.iter().rev().copied() {
            if ancestor_i > 0 {
                // We came from the right at this ancestor, so predecessor is at ancestor_i - 1
                // SAFETY: The ancestor pointer was stored during tree traversal and points
                // to a valid node in the tree with the same lifetime as self.
                let ancestor = unsafe { &*ancestor_ptr };
                return Some((ancestor, ancestor_i - 1));
            }
        }

        // No predecessor found - this is the minimum key
        None
    }

    /// Returns a reference to the node and index of the entry immediately above (successor of)
    /// this occupied entry. Returns `None` if this entry is the maximum key.
    fn index_above(&self) -> Option<(&Node<K, V, B>, usize)> {
        // Check if successor is in current node
        if self.i + 1 < self.node.n_keys() {
            return Some((&*self.node, self.i + 1));
        }

        // Walk up ancestors to find successor
        for (ancestor_ptr, ancestor_i) in self.ancestors.iter().rev().copied() {
            // SAFETY: The ancestor pointer was stored during tree traversal and points
            // to a valid node in the tree with the same lifetime as self.
            let ancestor = unsafe { &*ancestor_ptr };
            if ancestor_i < ancestor.n_keys() {
                // We came from the left at this ancestor, so successor is at ancestor_i
                return Some((ancestor, ancestor_i));
            }
        }

        // No successor found - this is the maximum key
        None
    }

    /// Returns a reference to the key that is immediately below (predecessor of)
    /// this occupied entry's key in the tree's sorted order.
    /// Returns `None` if this entry is the minimum key.
    pub fn key_below(&self) -> Option<&K> {
        let (node, i) = self.index_below()?;
        Some(node.key_at(i))
    }

    /// Returns a reference to the key that is immediately above (successor of)
    /// this occupied entry's key in the tree's sorted order.
    /// Returns `None` if this entry is the maximum key.
    pub fn key_above(&self) -> Option<&K> {
        let (node, i) = self.index_above()?;
        Some(node.key_at(i))
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.node.value_at_mut(self.i)
    }

    pub fn into_mut(self) -> &'s mut V {
        self.node.value_at_mut(self.i)
    }

    pub fn insert(&mut self, mut value: V) -> V {
        core::mem::swap(&mut value, self.node.value_at_mut(self.i));
        value
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    pub unsafe fn remove<A: Allocator>(self, alloc: &A) -> ((K, V), bool) {
        // SAFETY: Caller ensures `alloc` is the same allocator used for the B-tree.
        let r = unsafe { self.node.remove_from_here_in(alloc, self.i) };

        for (parent, j) in self.ancestors.iter().rev().copied() {
            // SAFETY: Parent pointer is valid for the tree's lifetime.
            let parent: &mut Node<K, V, B> = unsafe { &mut *parent };
            if !parent.check_underflow(alloc, j) {
                return (r, false);
            }
        }

        (r, true)
    }
}

// impl<
//         's,
//         K: core::cmp::PartialOrd + core::fmt::Debug,
//         Q: core::cmp::PartialOrd,
//         V,
//         B: ArrayLength,
//         NR: NodeRef<'s, K, V, B>,
//     > NodeEntry<'s, K, Q, V, B, NR>
// where
//     U2: Mul<B>,
//     Prod<U2, B>: ArrayLength,
//     U1: Add<Prod<U2, B>>,
//     Sum<U1, Prod<U2, B>>: ArrayLength,
//     K: Borrow<Q>,
// {
//     #[inline]
//     fn key(&self) -> &Q {
//         match self {
//             Self::Occupied(o) => o.key().borrow(),
//             Self::Vacant(v) => v.key(),
//         }
//     }
// }

// impl<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
//     NodeEntry<'s, K, K, V, B, &'s mut Node<K, V, B>>
// where
//     U2: Mul<B>,
//     Prod<U2, B>: ArrayLength,
//     U1: Add<Prod<U2, B>>,
//     Sum<U1, Prod<U2, B>>: ArrayLength,
// {
//     fn and_modify<F>(self, f: F) -> Self
//     where
//         F: FnOnce(&mut V),
//     {
//         match self {
//             Self::Occupied(mut o) => {
//                 f(o.get_mut());
//                 Self::Occupied(o)
//             }
//             Self::Vacant(v) => Self::Vacant(v),
//         }
//     }

//     fn or_default_in<'a, A: Allocator>(
//         self,
//         alloc: &'a A,
//     ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>>
//     where
//         V: Default,
//     {
//         match self {
//             Self::Occupied(o) => Ok(InsertOption::NewKey(o.into_mut())),
//             Self::Vacant(v) => v.insert_in(alloc, V::default()),
//         }
//     }

//     fn or_insert_in<'a, A: Allocator>(
//         self,
//         alloc: &'a A,
//         default: V,
//     ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
//         match self {
//             Self::Occupied(o) => Ok(InsertOption::NewKey(o.into_mut())),
//             Self::Vacant(v) => v.insert_in(alloc, default),
//         }
//     }

//     fn or_insert_with_in<'a, F, A: Allocator>(
//         self,
//         alloc: &'a A,
//         default: F,
//     ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>>
//     where
//         F: FnOnce() -> V,
//     {
//         match self {
//             Self::Occupied(o) => Ok(InsertOption::NewKey(o.into_mut())),
//             Self::Vacant(v) => v.insert_in(alloc, default()),
//         }
//     }

//     fn or_insert_with_key_in<'a, F, A: Allocator>(
//         self,
//         alloc: &'a A,
//         default: F,
//     ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>>
//     where
//         F: FnOnce(&K) -> V,
//     {
//         match self {
//             Self::Occupied(o) => Ok(InsertOption::NewKey(o.into_mut())),
//             Self::Vacant(v) => {
//                 let new_value = default(v.key());
//                 v.insert_in(alloc, new_value)
//             }
//         }
//     }
// }
