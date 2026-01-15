use core::borrow::Borrow;
use core::fmt::Debug;
use core::ops::Add;
use core::ops::Deref;
use core::ops::Mul;

extern crate alloc;
use alloc::vec::Vec;

use allocator_api2::alloc::Allocator;

use generic_array::ArrayLength;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use allocated::AllocResult;

use super::child_ptr::ChildPtr;
use super::InsertOption;
use super::{
    DropGuardNode, InteriorNode, LeafNode, Node, NodeEntry, OccupiedNodeEntry, VacantNodeEntry,
};

pub enum NodeRefType {
    Interior,
    Leaf,
}

pub enum MutNodeRef<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    Interior(&'a mut InteriorNode<K, V, B>),
    Leaf(&'a mut LeafNode<K, V, B>),
}

impl<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> MutNodeRef<'s, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn into_interior_node(self) -> &'s mut InteriorNode<K, V, B> {
        match self {
            Self::Interior(n) => n,
            Self::Leaf(_) => panic!("Not an interior node"),
        }
    }

    /// # Safety
    ///
    /// `parents` must be the ancestors of this node.
    pub unsafe fn entry_in(
        self,
        key: K,
        parents: Vec<(ChildPtr, usize)>,
    ) -> NodeEntry<'s, K, K, V, B, MutNodeRef<'s, K, V, B>> {
        match self {
            // SAFETY: Caller guarantees `parents` are the ancestors of this node
            Self::Interior(n) => unsafe { n.entry_in(key, parents) },
            // SAFETY: Caller guarantees `parents` are the ancestors of this node
            Self::Leaf(n) => unsafe { n.entry_in(key, parents) },
        }
    }

    pub fn merge(&mut self, pair: (K, V), rhs: Node<K, V, B>) {
        match (self, rhs) {
            (Self::Interior(n), Node::Interior(rhs)) => n.merge(pair, rhs),
            (Self::Leaf(n), Node::Leaf(rhs)) => n.merge(pair, rhs),
            _ => panic!("Mismatched node types"),
        }
    }

    pub fn value_at_mut(&mut self, i: usize) -> &mut V {
        match self {
            Self::Interior(n) => n.value_at_mut(i),
            Self::Leaf(n) => n.value_at_mut(i),
        }
    }

    pub fn into_value_at_mut(self, i: usize) -> &'s mut V {
        match self {
            Self::Interior(n) => n.value_at_mut(i),
            Self::Leaf(n) => n.value_at_mut(i),
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn remove_from_here_in<A: Allocator>(&mut self, alloc: &A, i: usize) -> (K, V) {
        match self {
            // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
            Self::Interior(n) => unsafe { n.remove_from_here_in(alloc, i) },
            // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
            Self::Leaf(n) => unsafe { n.remove_from_here_in(alloc, i) },
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn insert_in_here<'a, A: Allocator>(
        self,
        alloc: &'a A,
        key: K,
        value: V,
        i: usize,
        rhn: Option<DropGuardNode<'a, K, V, B, A>>,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        match self {
            Self::Interior(n) => {
                assert!(rhn.is_some());
                // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
                unsafe { n.insert_in_here(alloc, key, value, i, rhn.unwrap()) }
            }
            Self::Leaf(n) => {
                assert!(rhn.is_none());
                // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
                unsafe { n.insert_in_here(alloc, key, value, i) }
            }
        }
    }

    pub fn take_last_child(&mut self) -> ((K, V), ChildPtr) {
        match self {
            Self::Interior(n) => n.take_last_child(),
            Self::Leaf(n) => n.take_last_child(),
        }
    }

    pub fn insert_first_entry(&mut self, entry: (K, V), child: ChildPtr) {
        match self {
            Self::Interior(n) => n.insert_first_entry(entry, child),
            Self::Leaf(n) => n.insert_first_entry(entry, child),
        }
    }

    pub fn insert_last_entry(&mut self, entry: (K, V), child: ChildPtr) {
        match self {
            Self::Interior(n) => n.insert_last_entry(entry, child),
            Self::Leaf(n) => n.insert_last_entry(entry, child),
        }
    }

    pub fn take_first_child(&mut self) -> ((K, V), ChildPtr) {
        match self {
            Self::Interior(n) => n.take_first_child(),
            Self::Leaf(n) => n.take_first_child(),
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn remove_first_child<A: Allocator>(&mut self, alloc: &A) -> (K, V) {
        match self {
            // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
            Self::Interior(n) => unsafe { n.remove_first_child(alloc) },
            // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
            Self::Leaf(n) => unsafe { n.remove_first_child(alloc) },
        }
    }
}

#[derive(Debug)]
pub enum NodeRef<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    Interior(&'a InteriorNode<K, V, B>),
    Leaf(&'a LeafNode<K, V, B>),
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeRef<'a, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Clone
    for NodeRef<'a, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn clone(&self) -> Self {
        match self {
            Self::Interior(n) => Self::Interior(n),
            Self::Leaf(n) => Self::Leaf(n),
        }
    }
}

#[allow(clippy::module_name_repetitions)]
pub trait NodeRefT<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>:
    Sized
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    // type NodeRef;
    type KeyRef: 'n + Deref<Target = K>;
    type ValueRef: 'n + Deref<Target = V>;

    /// # Safety
    ///
    /// Caller must ensure mutability matches.
    unsafe fn from_ptr(p: ChildPtr) -> Self;
    fn as_ptr(&mut self) -> ChildPtr;

    fn as_type(&self) -> NodeRefType;

    fn find<Q>(&self, search_key: &Q) -> (usize, bool)
    where
        K: Borrow<Q> + PartialOrd,
        Q: PartialOrd + ?Sized + core::fmt::Debug;

    fn n_keys(&self) -> usize;
    fn is_leaf(&self) -> bool;
    fn key_at(&self, i: usize) -> &K;
    fn value_at(&self, i: usize) -> &V;
    fn child_at(&self, i: usize) -> Option<NodeRef<'_, K, V, B>>;

    fn into_value_at(self, i: usize) -> &'n V;
    fn into_key_value_at(self, i: usize) -> (&'n K, Self::ValueRef);
    fn into_child_at(self, i: usize) -> Option<Self>;

    fn first_entry_in(
        mut self,
        mut parents: Vec<(ChildPtr, usize)>,
    ) -> OccupiedNodeEntry<'n, K, V, B, Self>
    where
        Self: Sized,
    {
        match self.as_type() {
            NodeRefType::Interior => {
                parents.push((self.as_ptr(), 0));
                self.into_child_at(0).unwrap().first_entry_in(parents)
            }
            NodeRefType::Leaf => OccupiedNodeEntry::new(parents, self, 0),
        }
    }

    fn last_entry_in(
        mut self,
        mut parents: Vec<(ChildPtr, usize)>,
    ) -> OccupiedNodeEntry<'n, K, V, B, Self>
    where
        Self: Sized,
    {
        match self.as_type() {
            NodeRefType::Interior => {
                let n = self.n_keys();
                parents.push((self.as_ptr(), n));
                self.into_child_at(n).unwrap().last_entry_in(parents)
            }
            NodeRefType::Leaf => {
                let n = self.n_keys();
                OccupiedNodeEntry::new(parents, self, n - 1)
            }
        }
    }

    fn ref_entry<'s, Q>(
        mut self,
        key: &'s Q,
        mut parents: Vec<(ChildPtr, usize)>,
    ) -> NodeEntry<'n, K, &'s Q, V, B, Self>
    where
        K: Borrow<Q> + core::cmp::PartialOrd,
        Q: core::cmp::PartialOrd + core::fmt::Debug + ?Sized,
    {
        let (i, match_) = self.find(key);

        if match_ {
            return NodeEntry::Occupied(OccupiedNodeEntry::new(parents, self, i));
        }

        // Check if child exists before consuming self
        match self.child_at(i) {
            None => {
                // Child doesn't exist - create vacant entry at this node
                NodeEntry::Vacant(VacantNodeEntry::<K, &Q, V, B, Self>::new(key, parents, self, i))
            }
            Some(_) => {
                // Child exists - descend into it
                parents.push((self.as_ptr(), i));
                let child = self.into_child_at(i).unwrap();
                child.ref_entry(key, parents)
            }
        }
    }
}

impl<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeRefT<'n, K, V, B>
    for NodeRef<'n, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type KeyRef = &'n K;
    type ValueRef = &'n V;

    unsafe fn from_ptr(p: ChildPtr) -> Self {
        // SAFETY: Requires p is a valid ChildPtr with appropriate lifetime
        unsafe { p.unsafe_as_node_ref() }
    }

    fn as_ptr(&mut self) -> ChildPtr {
        ChildPtr::from_node_ref(self.clone())
    }

    fn into_value_at(self, i: usize) -> &'n V {
        match self {
            NodeRef::Interior(node) => node.value_at(i),
            NodeRef::Leaf(node) => node.value_at(i),
        }
    }

    fn into_key_value_at(self, i: usize) -> (&'n K, Self::ValueRef) {
        match self {
            NodeRef::Interior(node) => node.key_value_at(i),
            NodeRef::Leaf(node) => node.key_value_at(i),
        }
    }

    fn into_child_at(self, i: usize) -> Option<Self> {
        match self {
            NodeRef::Interior(node) => node.child_at(i),
            NodeRef::Leaf(_) => None,
        }
    }

    fn n_keys(&self) -> usize {
        match self {
            NodeRef::Interior(node) => node.n_keys(),
            NodeRef::Leaf(node) => node.n_keys(),
        }
    }

    fn find<Q>(&self, search_key: &Q) -> (usize, bool)
    where
        K: Borrow<Q> + PartialOrd,
        Q: PartialOrd + ?Sized + core::fmt::Debug,
    {
        match self {
            NodeRef::Interior(node) => node.find(search_key),
            NodeRef::Leaf(node) => node.find(search_key),
        }
    }
    fn is_leaf(&self) -> bool {
        match self {
            NodeRef::Interior(_) => false,
            NodeRef::Leaf(_) => true,
        }
    }

    fn key_at(&self, i: usize) -> &K {
        match self {
            NodeRef::Interior(n) => n.key_at(i),
            NodeRef::Leaf(n) => n.key_at(i),
        }
    }

    fn value_at(&self, i: usize) -> &V {
        match self {
            NodeRef::Interior(n) => n.value_at(i),
            NodeRef::Leaf(n) => n.value_at(i),
        }
    }

    fn child_at(&self, i: usize) -> Option<NodeRef<'_, K, V, B>> {
        match self {
            NodeRef::Interior(n) => n.child_at(i),
            NodeRef::Leaf(_) => None,
        }
    }

    fn as_type(&self) -> NodeRefType {
        match self {
            NodeRef::Interior(_) => NodeRefType::Interior,
            NodeRef::Leaf(_) => NodeRefType::Leaf,
        }
    }
}

impl<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeRefT<'n, K, V, B>
    for MutNodeRef<'n, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type KeyRef = &'n K;
    // type NodeRef = NodeRef<'n, K, V, B>;
    type ValueRef = &'n mut V;

    unsafe fn from_ptr(p: ChildPtr) -> Self {
        // SAFETY: Requires p is a valid ChildPtr with appropriate lifetime and exclusive access
        unsafe { p.unsafe_as_mut_node_ref() }
    }

    fn as_ptr(&mut self) -> ChildPtr {
        ChildPtr::from_mut_node_ref(self)
    }

    fn into_value_at(self, i: usize) -> &'n V {
        match self {
            MutNodeRef::Interior(node) => node.value_at(i),
            MutNodeRef::Leaf(node) => node.value_at(i),
        }
    }

    fn into_key_value_at(self, i: usize) -> (&'n K, Self::ValueRef) {
        match self {
            MutNodeRef::Interior(node) => node.key_value_mut_at(i),
            MutNodeRef::Leaf(node) => node.key_value_mut_at(i),
        }
    }

    fn into_child_at(self, i: usize) -> Option<Self> {
        match self {
            MutNodeRef::Interior(node) => node.child_at_mut(i),
            MutNodeRef::Leaf(_) => None,
        }
    }

    fn n_keys(&self) -> usize {
        match self {
            MutNodeRef::Interior(node) => node.n_keys(),
            MutNodeRef::Leaf(node) => node.n_keys(),
        }
    }

    fn find<Q>(&self, search_key: &Q) -> (usize, bool)
    where
        K: Borrow<Q> + PartialOrd,
        Q: PartialOrd + ?Sized + core::fmt::Debug,
    {
        match self {
            MutNodeRef::Interior(node) => node.find(search_key),
            MutNodeRef::Leaf(node) => node.find(search_key),
        }
    }
    fn is_leaf(&self) -> bool {
        match self {
            MutNodeRef::Interior(_) => false,
            MutNodeRef::Leaf(_) => true,
        }
    }

    fn key_at(&self, i: usize) -> &K {
        match self {
            MutNodeRef::Interior(n) => n.key_at(i),
            MutNodeRef::Leaf(n) => n.key_at(i),
        }
    }
    fn value_at(&self, i: usize) -> &V {
        match self {
            MutNodeRef::Interior(n) => n.value_at(i),
            MutNodeRef::Leaf(n) => n.value_at(i),
        }
    }

    fn child_at(&self, i: usize) -> Option<NodeRef<'_, K, V, B>> {
        match self {
            MutNodeRef::Interior(n) => n.child_at(i),
            MutNodeRef::Leaf(_) => None,
        }
    }

    fn as_type(&self) -> NodeRefType {
        match self {
            MutNodeRef::Interior(_) => NodeRefType::Interior,
            MutNodeRef::Leaf(_) => NodeRefType::Leaf,
        }
    }
}
