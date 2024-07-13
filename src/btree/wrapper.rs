//! Ergonomic wrapper for the naive B-Tree implementation.
//!
//! This module provides [`NaiveBTreeMap<K, V, B, A>`], a wrapper around
//! [`AllocatedBTreeMap`] that owns an allocator, making it safe and
//! ergonomic to use.

use core::borrow::Borrow;
use core::fmt::Debug;
use core::mem::ManuallyDrop;
use core::ops::Add;
use core::ops::Mul;

use allocator_api2::alloc::{Allocator, Global};
use generic_array::ArrayLength;
use typenum::{Prod, Sum, U1, U2, U6};

use allocated::{AllocResult, AllocResultExt, DropIn};

use super::{AllocatedBTreeMap, Entry, Iter, Keys, OccupiedEntry, Values, ValuesMut};

/// An ergonomic B-Tree map that owns its allocator.
///
/// This is the recommended type for most use cases. It wraps
/// [`AllocatedBTreeMap`] and provides safe methods without requiring
/// `unsafe` blocks or passing allocators manually.
///
/// # Example
///
/// ```
/// use allocated_btree::NaiveBTreeMap;
///
/// let mut map = NaiveBTreeMap::new();
/// map.insert(1, "one").unwrap();
/// map.insert(2, "two").unwrap();
///
/// assert_eq!(map.get(&1), Some(&"one"));
/// assert_eq!(map.len(), 2);
/// ```
pub struct NaiveBTreeMap<
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength = U6,
    A: Allocator = Global,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    alloc: A,
    raw: ManuallyDrop<AllocatedBTreeMap<K, V, B>>,
}

impl<K: core::cmp::PartialOrd + Debug, V> NaiveBTreeMap<K, V> {
    /// Create a new empty B-Tree using the global allocator.
    ///
    /// # Panics
    ///
    /// Panics if allocation fails.
    #[inline]
    pub fn new() -> Self {
        let raw = AllocatedBTreeMap::new_in(&Global)
            .handle_alloc_error()
            .into_inner();

        Self { alloc: Global, raw }
    }
}

impl<K: core::cmp::PartialOrd + Debug, V> Default for NaiveBTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: core::cmp::PartialOrd + Debug, V, B: ArrayLength, A: Allocator> Drop
    for NaiveBTreeMap<K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn drop(&mut self) {
        // SAFETY: `self.raw` was allocated by `self.alloc`
        unsafe {
            self.raw.drop_in(&self.alloc);
        }
    }
}

impl<K: core::cmp::PartialOrd + Debug, V, B: ArrayLength, A: Allocator> NaiveBTreeMap<K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Create a new empty B-Tree using the provided allocator.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails.
    pub fn new_in(alloc: A) -> AllocResult<Self> {
        let raw = AllocatedBTreeMap::new_in(&alloc)?.into_inner();
        Ok(Self { alloc, raw })
    }

    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Returns `true` if the map contains a value for the specified key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: core::cmp::PartialOrd + Debug,
    {
        self.raw.contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: core::cmp::PartialOrd + Debug,
    {
        self.raw.get(key)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    pub fn get_key_value<'s, Q>(&'s self, key: &'s Q) -> Option<(&'s K, &'s V)>
    where
        K: Borrow<Q>,
        Q: core::cmp::PartialOrd + Debug,
    {
        self.raw.get_key_value(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<'s, Q>(&'s mut self, key: &'s Q) -> Option<&'s mut V>
    where
        K: Borrow<Q>,
        Q: core::cmp::PartialOrd + Debug,
    {
        self.raw.get_mut(key)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated,
    /// and the old value is returned.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails during tree rebalancing.
    pub fn insert(&mut self, key: K, value: V) -> AllocResult<Option<V>> {
        // SAFETY: `self.alloc` was used to allocate `self.raw`
        unsafe { self.raw.insert_in(&self.alloc, key, value) }
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails.
    pub fn clear(&mut self) -> AllocResult<()> {
        // SAFETY: `self.alloc` was used to allocate `self.raw`
        unsafe { self.raw.clear_in(&self.alloc) }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    pub fn entry(&mut self, key: K) -> Entry<'_, '_, A, K, V, B> {
        // SAFETY: `self.alloc` was used to allocate `self.raw`
        unsafe { self.raw.entry_in(&self.alloc, key) }
    }

    /// Gets the first entry in the map for in-place manipulation.
    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, '_, A, K, V, B>> {
        // SAFETY: `self.alloc` was used to allocate `self.raw`
        unsafe { self.raw.first_entry_in(&self.alloc) }
    }

    /// Returns the first key-value pair in the map.
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.raw.first_key_value()
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    pub fn iter(&self) -> Iter<'_, K, V, B> {
        self.raw.iter()
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    pub fn keys(&self) -> Keys<'_, K, V, B> {
        self.raw.keys()
    }

    /// Gets an iterator over the values of the map, in order by key.
    pub fn values(&self) -> Values<'_, K, V, B> {
        self.raw.values()
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, B> {
        self.raw.values_mut()
    }
}

impl<'s, K: core::cmp::PartialOrd + Debug, V, B: ArrayLength, A: Allocator> IntoIterator
    for &'s NaiveBTreeMap<K, V, B, A>
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
