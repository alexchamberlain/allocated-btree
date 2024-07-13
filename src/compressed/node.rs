use core::fmt;
use core::mem::MaybeUninit;
use core::ops::Add;
use core::ops::Mul;

use allocated::DropGuard;
use allocated::DropIn;
use allocator_api2::alloc::Allocator;
use generic_array::ArrayLength;
use generic_array::GenericArray;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

mod child_ptr;
mod entry;
mod interior_node;
mod iter;
mod leaf_node;
mod node_ref;

#[allow(clippy::module_name_repetitions)]
pub use entry::{NodeEntry, OccupiedNodeEntry, VacantNodeEntry};
pub use iter::{IntoIter, Iter};

pub use child_ptr::ChildPtr;
pub use interior_node::InteriorNode;
pub use leaf_node::LeafNode;
pub use node_ref::{MutNodeRef, NodeRef, NodeRefT};

type Keys<K, B> = GenericArray<MaybeUninit<K>, Prod<U2, B>>;
type Values<V, B> = GenericArray<MaybeUninit<V>, Prod<U2, B>>;
type Children<B> = GenericArray<ChildPtr, Sum<U1, Prod<U2, B>>>;

type DropGuardNode<'a, K, V, B, A> = DropGuard<Node<K, V, B>, &'a A>;

pub enum Node<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    Interior(InteriorNode<K, V, B>),
    Leaf(LeafNode<K, V, B>),
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn into_interior_node(self) -> InteriorNode<K, V, B> {
        match self {
            Self::Interior(n) => n,
            Self::Leaf(_) => panic!("Not an interior node"),
        }
    }

    pub fn as_ref(&self) -> NodeRef<'_, K, V, B> {
        match self {
            Self::Interior(n) => NodeRef::Interior(n),
            Self::Leaf(n) => NodeRef::Leaf(n),
        }
    }

    pub fn as_mut(&mut self) -> MutNodeRef<'_, K, V, B> {
        match self {
            Self::Interior(n) => MutNodeRef::Interior(n),
            Self::Leaf(n) => MutNodeRef::Leaf(n),
        }
    }

    pub fn n_keys(&self) -> usize {
        match self {
            Self::Interior(n) => n.n_keys(),
            Self::Leaf(n) => n.n_keys(),
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self {
            Self::Interior(n) => n.is_leaf(),
            Self::Leaf(n) => n.is_leaf(),
        }
    }

    pub fn take_key_value_at(&mut self, i: usize) -> (K, V) {
        match self {
            Self::Interior(n) => n.take_key_value_at(i),
            Self::Leaf(n) => n.take_key_value_at(i),
        }
    }

    pub fn key_at(&self, i: usize) -> &K {
        match self {
            Self::Interior(n) => n.key_at(i),
            Self::Leaf(n) => n.key_at(i),
        }
    }

    pub fn value_at(&self, i: usize) -> &V {
        match self {
            Self::Interior(n) => n.value_at(i),
            Self::Leaf(n) => n.value_at(i),
        }
    }

    pub fn value_at_mut(&mut self, i: usize) -> &mut V {
        match self {
            Self::Interior(n) => n.value_at_mut(i),
            Self::Leaf(n) => n.value_at_mut(i),
        }
    }

    pub fn child_at(&self, i: usize) -> Option<NodeRef<'_, K, V, B>> {
        match self {
            Self::Interior(n) => n.child_at(i),
            Self::Leaf(_) => None,
        }
    }
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> DropIn for Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    unsafe fn drop_in<A: Allocator>(&mut self, alloc: &A) {
        match self {
            // SAFETY: Caller guarantees `alloc` is the allocator used for this node
            Self::Interior(n) => unsafe { n.drop_in(alloc) },
            // SAFETY: Caller guarantees `alloc` is the allocator used for this node
            Self::Leaf(n) => unsafe { n.drop_in(alloc) },
        }
    }
}

pub enum InsertOption<
    'a,
    's,
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
    NewKey(&'s mut V),
    Split((K, V, DropGuardNode<'a, K, V, B, A>)),
}

impl<'a, 's, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: Allocator>
    InsertOption<'a, 's, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn is_new_key(&self) -> bool {
        matches!(self, Self::NewKey(_))
    }
}

impl<'a, 's, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: Allocator>
    fmt::Debug for InsertOption<'a, 's, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NewKey(_) => write!(f, "InsertOption::NewKey"),
            Self::Split((k, _, _)) => write!(f, "InsertOption::Split({k:?}...)"),
        }
    }
}

pub trait NodeT<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>: Sized
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
}

impl<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeT<'n, K, V, B>
    for InteriorNode<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
}

impl<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeT<'n, K, V, B>
    for LeafNode<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
}
