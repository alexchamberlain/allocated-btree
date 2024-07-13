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
    nodes: Vec<NR::Ptr>,
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
    pub(super) fn new(key: Q, nodes: Vec<NR::Ptr>, i: usize) -> Self
    where
        Q: Debug,
    {
        // println!("VacantNode key={:?}", key);

        Self {
            key,
            nodes,
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
    /// Inserts a value into the vacant entry.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `alloc` is the same allocator instance used
    /// to construct the B-tree. Using a different allocator will result in
    /// undefined behavior.
    pub unsafe fn insert_in<'a, A: Allocator>(
        mut self,
        alloc: &'a A,
        mut value: V,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let mut key = self.key;
        let mut i = Some(self.i);
        let mut rhn = None;
        while let Some(node) = self.nodes.pop() {
            // SAFETY: The node pointer came from the entry path traversal and is valid
            // for the lifetime 's. We have exclusive access through the entry.
            let node = unsafe { &mut *node };

            if i.is_none() {
                let (j, match_) = node.find(&key);
                assert!(!match_);
                i = Some(j);
            }

            // SAFETY: `alloc` is the same allocator used to create the B-tree (caller requirement).
            // The index `i` is valid from the find operation above.
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
