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
    nodes: Vec<ChildPtr>,
    i: usize,
    phantom1: PhantomData<&'s Node<K, V, B>>,
    phantom2: PhantomData<NR>,
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
    ancestors: Vec<(ChildPtr, usize)>,
    node: NR,
    i: usize,
    phantom1: PhantomData<&'s Node<K, V, B>>,
    phantom2: PhantomData<NR>,
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
    pub(super) fn new(key: Q, nodes: Vec<ChildPtr>, i: usize) -> Self {
        Self {
            key,
            nodes,
            i,
            phantom1: PhantomData,
            phantom2: PhantomData,
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
    VacantNodeEntry<'s, K, K, V, B, MutNodeRef<'s, K, V, B>>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn insert_in<'a, A: Allocator>(
        mut self,
        alloc: &'a A,
        mut value: V,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let mut key = self.key;
        let mut i = Some(self.i);
        let mut rhn = None;
        while let Some(node) = self.nodes.pop() {
            let node = node.as_mut_node_ref();

            if i.is_none() {
                let (j, match_) = node.find(&key);
                assert!(!match_);
                i = Some(j);
            }
            // SAFETY: Caller ensures alloc matches the allocator used for this tree
            let r = unsafe { node.insert_in_here(alloc, key, value, i.unwrap(), rhn)? };
            match r {
                InsertOption::NewKey(v) => {
                    return Ok(InsertOption::NewKey(v));
                }
                InsertOption::Split((k, v, new_rhn)) => {
                    key = k;
                    value = v;
                    rhn = Some(new_rhn);
                    i = None;
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
            phantom1: PhantomData,
            phantom2: PhantomData,
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
