#![allow(dead_code)]

use core::borrow::Borrow;
use core::fmt::Debug;
use core::mem::ManuallyDrop;
use core::ops::Add;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Mul;
use core::ptr::NonNull;

#[cfg(feature = "std")]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use alloc::string::String;
#[cfg(feature = "std")]
use std::error::Error;
#[cfg(feature = "std")]
use std::io::Write;

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;

use allocator_api2::alloc::Allocator;
use generic_array::ArrayLength;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;
use typenum::U6;

use allocated::AllocResult;
use allocated::DropGuard;
use allocated::DropGuardResult;
use allocated::DropIn;
use allocated::FromIteratorIn;
use allocated::IntoIteratorIn;

mod entry;
mod iters;
mod node;
mod wrapper;

#[cfg(test)]
mod tests;

pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use iters::{IntoIter, IntoKeys, IntoValues, Iter, Keys, Values, ValuesMut};
use node::{
    IntoIter as NodeIntoIter, Iter as NodeIter, Node, NodeEntry, NodeRef, OccupiedNodeEntry,
};
pub use wrapper::NaiveBTreeMap;

/// A B-Tree map implementation using the allocated pattern.
///
/// This is the low-level "allocated" type that requires manual allocator passing.
/// For most use cases, prefer the [`NaiveBTreeMap`] wrapper which owns its allocator
/// and provides a safe, ergonomic API.
///
/// # Type Parameters
///
/// - `K`: Key type, must be `PartialOrd + Debug`
/// - `V`: Value type
/// - `B`: Branching factor (defaults to `U6` for 6-way tree). Controls the number
///   of keys per node (2*B keys maximum).
///
/// # Examples
///
/// ```
/// use allocated_btree::AllocatedNaiveBTreeMap;
/// use allocated::CountingAllocator;
///
/// let alloc = CountingAllocator::default();
/// let mut map = AllocatedNaiveBTreeMap::<u32, String>::new_in(&alloc)?;
///
/// unsafe {
///     map.insert_in(&alloc, 1, "one".to_string())?;
///     map.insert_in(&alloc, 2, "two".to_string())?;
/// }
///
/// assert_eq!(map.len(), 2);
/// # Ok::<(), allocated::AllocErrorWithLayout>(())
/// ```
pub struct AllocatedBTreeMap<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength = U6>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    root: Option<ManuallyDrop<Node<K, V, B>>>,
    n: usize,
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> AllocatedBTreeMap<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// # Errors
    ///
    /// Will return `Err` if the allocation fails.
    pub fn new_in<A: Allocator>(alloc: &A) -> DropGuardResult<Self, &A> {
        Ok(Node::new_in(alloc).map(|root| AllocatedBTreeMap {
            root: Some(ManuallyDrop::new(root)),
            n: 0,
        }))
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Returns `true` if the map contains a value for the specified key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + core::cmp::PartialOrd,
        Q: core::cmp::PartialOrd + Debug,
    {
        let root = self.root.as_ref().unwrap();
        match root.ref_entry(key, vec![]) {
            NodeEntry::Vacant(_) => false,
            NodeEntry::Occupied(_) => true,
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated and the old value is returned.
    ///
    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    ///
    /// # Errors
    ///
    /// Will return `Err` if the allocation fails.
    pub unsafe fn insert_in<A: Allocator>(
        &mut self,
        alloc: &A,
        key: K,
        value: V,
    ) -> AllocResult<Option<V>>
    where
        K: Debug,
    {
        // Safety: requirements match function requirements
        let entry = unsafe { self.entry_in(alloc, key) };

        entry.insert(value)
    }

    /// Clears the map, removing all elements.
    ///
    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    ///
    /// # Errors
    ///
    /// Will return `Err` if the allocation fails.
    pub unsafe fn clear_in<A: Allocator>(&mut self, alloc: &A) -> AllocResult<()> {
        // Safety: requirements match function requirements
        unsafe {
            if let Some(mut r) = self.root.take() {
                r.drop_in(alloc);
            }
        }
        self.n = 0;
        self.root = Some(Node::new_in(alloc).into_inner());
        Ok(())
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get<'s, Q>(&'s self, key: &Q) -> Option<&'s V>
    where
        K: Borrow<Q> + core::cmp::PartialOrd,
        Q: core::cmp::PartialOrd + Debug,
    {
        let root = self.root.as_ref().unwrap();
        match root.ref_entry(key, vec![]) {
            NodeEntry::Vacant(_) => None,
            NodeEntry::Occupied(o) => Some(o.into_value()),
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    pub fn get_key_value<'s, Q>(&'s self, key: &'s Q) -> Option<(&'s K, &'s V)>
    where
        K: Borrow<Q> + core::cmp::PartialOrd,
        Q: core::cmp::PartialOrd + Debug,
    {
        let root = self.root.as_ref().unwrap();
        match root.ref_entry(key, vec![]) {
            NodeEntry::Vacant(_) => None,
            NodeEntry::Occupied(o) => Some(o.into_key_value()),
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<'s, Q>(&'s mut self, key: &'s Q) -> Option<&'s mut V>
    where
        K: Borrow<Q> + core::cmp::PartialOrd,
        Q: core::cmp::PartialOrd + Debug,
    {
        let root: &'s mut Node<K, V, B> = self.root.as_mut().unwrap();
        match root.ref_entry(key, vec![]) {
            NodeEntry::Vacant(_) => None,
            NodeEntry::Occupied(o) => Some(o.into_mut()),
        }
    }

    /// Returns an iterator over the key-value pairs of the map, in sorted order by key.
    pub fn iter(&self) -> Iter<'_, K, V, B> {
        let mut stack = Vec::new();
        if self.n > 0 {
            stack.push((self.root.as_ref().unwrap().deref().as_ptr(), 0));
        }
        Iter {
            inner: NodeIter::new(stack),
        }
    }

    /// Returns an iterator over the keys of the map, in sorted order.
    pub fn keys(&self) -> Keys<'_, K, V, B> {
        let mut stack = Vec::new();
        if self.n > 0 {
            stack.push((self.root.as_ref().unwrap().deref().as_ptr(), 0));
        }
        Keys {
            inner: NodeIter::new(stack),
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    unsafe fn into_keys_in<A: Allocator>(self, alloc: &A) -> IntoKeys<'_, K, V, B, A> {
        IntoKeys {
            inner: NodeIntoIter::new(alloc, ManuallyDrop::into_inner(self.root.unwrap())),
        }
    }

    /// Returns an iterator over the values of the map, in order by key.
    pub fn values(&self) -> Values<'_, K, V, B> {
        let mut stack = Vec::new();
        if self.n > 0 {
            stack.push((self.root.as_ref().unwrap().deref().as_ptr(), 0));
        }
        Values {
            inner: NodeIter::new(stack),
        }
    }

    /// Returns a mutable iterator over the values of the map, in order by key.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, B> {
        let mut stack = Vec::new();
        if self.n > 0 {
            stack.push((self.root.as_mut().unwrap().deref_mut().as_ptr(), 0));
        }
        ValuesMut {
            inner: NodeIter::new(stack),
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    unsafe fn into_values_in<A: Allocator>(self, alloc: &A) -> IntoValues<'_, K, V, B, A> {
        IntoValues {
            inner: NodeIntoIter::new(alloc, ManuallyDrop::into_inner(self.root.unwrap())),
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    pub unsafe fn entry_in<'a, 's, A: Allocator>(
        &'s mut self,
        alloc: &'a A,
        key: K,
    ) -> Entry<'a, 's, A, K, V, B>
    where
        K: Debug,
    {
        let map: NonNull<AllocatedBTreeMap<K, V, B>> = NonNull::from_mut(self);
        let root = self.root.as_mut().unwrap();
        // Safety: The ancestors of root is empty vec.
        let inner_entry = unsafe { root.entry_in(key, vec![]) };
        Entry::new(alloc, inner_entry, map)
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    pub unsafe fn first_entry_in<'a, 's, A: Allocator>(
        &'s mut self,
        alloc: &'a A,
    ) -> Option<OccupiedEntry<'a, 's, A, K, V, B>> {
        if self.n == 0 {
            return None;
        }

        let map = NonNull::new(self)?;
        let root: &'s mut Node<K, V, B> = self.root.as_mut().unwrap();
        let inner_entry: OccupiedNodeEntry<'s, K, V, B, &'s mut Node<K, V, B>> =
            root.first_entry(vec![]);
        // Safety: Requirements match function requirements
        unsafe { Some(OccupiedEntry::new(alloc, inner_entry, map)) }
    }

    /// Returns a reference to the first key-value pair in the map.
    /// The key in this pair is the minimum key in the map.
    pub fn first_key_value<'s>(&'s self) -> Option<(&'s K, &'s V)> {
        if self.n == 0 {
            return None;
        }

        let root: &'s Node<K, V, B> = self.root.as_ref().unwrap();
        let inner_entry: OccupiedNodeEntry<'s, K, V, B, &'s Node<K, V, B>> =
            root.first_entry(vec![]);
        Some(inner_entry.into_key_value())
    }
}

#[cfg(feature = "std")]
impl<K: core::cmp::PartialOrd + Debug, V: Debug, B: ArrayLength> AllocatedBTreeMap<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn to_dot(&self) -> Result<String, Box<dyn Error>> {
        let mut data = Vec::default();

        data.write_all(b"digraph G {\n")?;
        data.write_all(b"rankdir=\"LR\";\n")?;
        self.root.as_ref().unwrap().to_dot(&mut data)?;
        data.write_all(b"}\n")?;

        Ok(String::from_utf8(data)?)
    }
}

impl<'a, K: core::cmp::PartialOrd + Debug, V, B: ArrayLength, A: Allocator>
    FromIteratorIn<'a, (K, V), A> for AllocatedBTreeMap<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn from_iter_in<T>(alloc: &'a A, iter: T) -> DropGuardResult<Self, &'a A>
    where
        T: IntoIterator<Item = (K, V)>,
    {
        let mut btree: DropGuard<Self, &'a A> = Self::new_in(alloc)?;

        for (k, v) in iter {
            // Safety: `alloc` was used to create the `btree`
            unsafe {
                btree.insert_in(alloc, k, v)?;
            }
        }

        Ok(btree)
    }
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> DropIn
    for AllocatedBTreeMap<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// # Safety
    ///
    /// `alloc` must be the allocator used to allocate this object.
    unsafe fn drop_in<A: Allocator>(&mut self, alloc: &A) {
        // SAFETY: requirements match function requirements
        unsafe {
            if let Some(r) = self.root.as_mut() {
                r.drop_in(alloc);
            }
        }
    }
}

impl<K, V, B> allocated::RecursiveDropIn for AllocatedBTreeMap<K, V, B>
where
    K: core::cmp::PartialOrd + core::fmt::Debug + DropIn,
    V: DropIn,
    B: ArrayLength,
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// # Safety
    ///
    /// `alloc` must be the allocator used to allocate this object.
    unsafe fn recursive_drop_in<A: Allocator>(&mut self, alloc: &A) {
        if let Some(root) = self.root.as_mut() {
            // SAFETY: We're taking ownership of the root to iterate over it.
            let root_owned = unsafe { ManuallyDrop::take(root) };
            // Recursively drop all keys and values in the tree
            for (mut k, mut v) in NodeIntoIter::new(alloc, root_owned) {
                // SAFETY: alloc is the same allocator used for the B-tree.
                unsafe { k.drop_in(alloc) };
                // SAFETY: alloc is the same allocator used for the B-tree.
                unsafe { v.drop_in(alloc) };
            }
        }
        // SAFETY: alloc is the same allocator used for the B-tree. The tree structure itself is dropped.
        unsafe { self.drop_in(alloc) };
    }
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: Allocator + 'a>
    IntoIteratorIn<'a, A> for AllocatedBTreeMap<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = (K, V);
    type IntoIter = IntoIter<'a, K, V, B, A>;

    unsafe fn into_iter_in(self, alloc: &'a A) -> Self::IntoIter {
        IntoIter {
            inner: NodeIntoIter::new(alloc, ManuallyDrop::into_inner(self.root.unwrap())),
        }
    }
}

impl<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> IntoIterator
    for &'s AllocatedBTreeMap<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type IntoIter = Iter<'s, K, V, B>;
    type Item = (&'s K, &'s V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
