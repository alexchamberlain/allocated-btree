//! Ergonomic wrapper for the compressed B-Tree implementation.
//!
//! This module provides [`CompressedBTreeMap<K, V, B, A>`], a wrapper around
//! the allocated B-Tree that owns an allocator, making it safe and
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

/// An ergonomic compressed B-Tree map that owns its allocator.
///
/// This is a memory-optimized B-Tree that uses specialized leaf nodes
/// without child pointers, reducing memory usage by approximately 30%
/// compared to the naive implementation.
///
/// This is the recommended type for most use cases. It wraps the allocated
/// B-Tree and provides safe methods without requiring `unsafe` blocks or
/// passing allocators manually.
///
/// # Example
///
/// ```
/// use allocated_btree::CompressedBTreeMap;
///
/// let mut map = CompressedBTreeMap::new();
/// map.insert(1, "one").unwrap();
/// map.insert(2, "two").unwrap();
///
/// assert_eq!(map.get(&1), Some(&"one"));
/// assert_eq!(map.len(), 2);
/// ```
pub struct CompressedBTreeMap<
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

impl<K: core::cmp::PartialOrd + Debug, V> CompressedBTreeMap<K, V> {
    /// Create a new empty compressed B-Tree using the global allocator.
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

impl<K: core::cmp::PartialOrd + Debug, V> Default for CompressedBTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: core::cmp::PartialOrd + Debug, V, B: ArrayLength, A: Allocator> Drop
    for CompressedBTreeMap<K, V, B, A>
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

impl<K: core::cmp::PartialOrd + Debug, V, B: ArrayLength, A: Allocator>
    CompressedBTreeMap<K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Create a new empty compressed B-Tree using the provided allocator.
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

    /// Gets the given key's corresponding occupied entry in the map for in-place manipulation.
    ///
    /// Returns `None` if the key is not present in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert(1, "a").unwrap();
    ///
    /// // Get the entry if it exists and modify it
    /// if let Some(mut entry) = map.entry_ref(&1) {
    ///     *entry.get_mut() = "b";
    /// }
    /// assert_eq!(map.get(&1), Some(&"b"));
    ///
    /// // Non-existent key returns None
    /// assert!(map.entry_ref(&2).is_none());
    /// ```
    ///
    /// Using `String` keys with `&str` lookups:
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert("hello".to_string(), 42).unwrap();
    ///
    /// if let Some(entry) = map.entry_ref("hello") {
    ///     assert_eq!(entry.key(), &"hello".to_string());
    /// }
    /// ```
    pub fn entry_ref<Q>(&mut self, key: &Q) -> Option<OccupiedEntry<'_, '_, A, K, V, B>>
    where
        K: Borrow<Q>,
        Q: PartialOrd + core::fmt::Debug + ?Sized,
    {
        // SAFETY: self.alloc was used to allocate self.raw
        unsafe { self.raw.entry_ref_in(&self.alloc, key) }
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

    /// Gets the last entry in the map for in-place manipulation.
    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, '_, A, K, V, B>> {
        // SAFETY: `self.alloc` was used to allocate `self.raw`
        unsafe { self.raw.last_entry_in(&self.alloc) }
    }

    /// Returns the last key-value pair in the map.
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.raw.last_key_value()
    }

    /// Returns the first key in the map.
    pub fn first(&self) -> Option<&K> {
        self.raw.first()
    }

    /// Returns the last key in the map.
    pub fn last(&self) -> Option<&K> {
        self.raw.last()
    }

    /// Removes and returns the first key-value pair in the map.
    /// The key in this pair is the minimum key that was in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert(1, "a").unwrap();
    /// map.insert(2, "b").unwrap();
    ///
    /// assert_eq!(map.pop_first(), Some((1, "a")));
    /// assert_eq!(map.pop_first(), Some((2, "b")));
    /// assert_eq!(map.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        self.first_entry().map(|entry| entry.remove_entry())
    }

    /// Removes and returns the last key-value pair in the map.
    /// The key in this pair is the maximum key that was in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert(1, "a").unwrap();
    /// map.insert(2, "b").unwrap();
    ///
    /// assert_eq!(map.pop_last(), Some((2, "b")));
    /// assert_eq!(map.pop_last(), Some((1, "a")));
    /// assert_eq!(map.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        self.last_entry().map(|entry| entry.remove_entry())
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    ///
    /// Using `String` keys with `&str` lookups:
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert("hello".to_string(), 42).unwrap();
    /// assert_eq!(map.remove("hello"), Some(42));  // Note: &str, not &String
    /// assert_eq!(map.remove("hello"), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: PartialOrd + core::fmt::Debug + ?Sized,
    {
        // SAFETY: self.alloc was used to allocate self.raw
        unsafe { self.raw.remove_in(&self.alloc, key) }
    }

    /// Removes a key from the map, returning the stored key and value if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&1), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: PartialOrd + core::fmt::Debug + ?Sized,
    {
        // SAFETY: self.alloc was used to allocate self.raw
        unsafe { self.raw.remove_entry_in(&self.alloc, key) }
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
    for &'s CompressedBTreeMap<K, V, B, A>
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

impl<K: PartialOrd + Debug, V> FromIterator<(K, V)> for CompressedBTreeMap<K, V> {
    /// Creates a B-tree map from an iterator of key-value pairs.
    ///
    /// If the iterator yields multiple values for the same key, the last value wins.
    ///
    /// # Panics
    ///
    /// Panics if allocation fails during construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let items = vec![(1, "a"), (2, "b"), (3, "c")];
    /// let map: CompressedBTreeMap<_, _> = items.into_iter().collect();
    ///
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), Some(&"b"));
    /// assert_eq!(map.get(&3), Some(&"c"));
    /// assert_eq!(map.len(), 3);
    /// ```
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        use allocated::{AllocResultExt, FromIteratorIn};
        use allocator_api2::alloc::Global;

        let alloc = Global;
        let raw = AllocatedBTreeMap::from_iter_in(&alloc, iter)
            .handle_alloc_error()
            .into_inner();
        Self { alloc, raw }
    }
}

impl<K: PartialOrd + Debug, V, B: ArrayLength, A: Allocator> Extend<(K, V)>
    for CompressedBTreeMap<K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Extends the map with the contents of an iterator.
    ///
    /// If the iterator yields duplicate keys, the last value wins.
    ///
    /// # Panics
    ///
    /// Panics if allocation fails during insertion.
    ///
    /// # Examples
    ///
    /// ```
    /// use allocated_btree::CompressedBTreeMap;
    ///
    /// let mut map = CompressedBTreeMap::new();
    /// map.insert(1, "a").unwrap();
    ///
    /// let more_items = vec![(2, "b"), (3, "c")];
    /// map.extend(more_items);
    ///
    /// assert_eq!(map.len(), 3);
    /// assert_eq!(map.get(&2), Some(&"b"));
    /// ```
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        use allocated::AllocResultExt;

        for (k, v) in iter {
            let _ = self.insert(k, v).handle_alloc_error();
        }
    }
}
