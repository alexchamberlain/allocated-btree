use core::fmt::Debug;
use core::mem::ManuallyDrop;
use core::ops::Add;
use core::ops::Mul;
use core::ptr::NonNull;

use allocated::AllocResult;
use allocator_api2::alloc::Allocator;
use generic_array::ArrayLength;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use super::node::InsertOption;
use super::node::InteriorNode;
use super::node::MutNodeRef;
use super::node::Node;
use super::node::NodeEntry;
use super::node::OccupiedNodeEntry;
use super::node::VacantNodeEntry;
use super::AllocatedBTreeMap;

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This enum is constructed from the [`entry`](super::wrapper::CompressedBTreeMap::entry) method on
/// [`CompressedBTreeMap`](super::wrapper::CompressedBTreeMap).
#[allow(clippy::module_name_repetitions)]
pub enum Entry<'a, 's, A: Allocator, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// A vacant entry.
    Vacant(VacantEntry<'a, 's, A, K, V, B>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, 's, A, K, V, B>),
}

/// A view into a vacant entry in a `CompressedBTreeMap`.
/// It is part of the [`Entry`] enum.
#[allow(clippy::module_name_repetitions)]
pub struct VacantEntry<
    'a,
    's,
    A: Allocator,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    alloc: &'a A,
    inner: VacantNodeEntry<'s, K, K, V, B, MutNodeRef<'s, K, V, B>>,
    map: NonNull<AllocatedBTreeMap<K, V, B>>,
}

/// A view into an occupied entry in a `CompressedBTreeMap`.
/// It is part of the [`Entry`] enum.
#[allow(clippy::module_name_repetitions)]
pub struct OccupiedEntry<
    'a,
    's,
    A: Allocator,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    alloc: &'a A,
    inner: OccupiedNodeEntry<'s, K, V, B, MutNodeRef<'s, K, V, B>>,
    map: NonNull<AllocatedBTreeMap<K, V, B>>,
}

impl<'a, 's, A: Allocator, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
    VacantEntry<'a, 's, A, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// Gets a reference to the key that would be used when inserting a value through the `VacantEntry`.
    pub fn key(&self) -> &K {
        self.inner.key()
    }

    /// Takes ownership of the key.
    pub fn into_key(self) -> K {
        self.inner.into_key()
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns `None`.
    ///
    /// # Errors
    ///
    /// Will return `Err` if the allocation fails.
    pub fn insert(mut self, value: V) -> AllocResult<Option<V>> {
        let alloc = self.alloc;
        let io = self.inner.insert_in(alloc, value)?;
        match io {
            InsertOption::NewKey(_) => {
                // SAFETY: Requires map is a valid non-null pointer with exclusive access
                unsafe { self.map.as_mut() }.n += 1;
                Ok(None)
            }
            InsertOption::Split((k, v, n)) => {
                // SAFETY: Requires map is a valid non-null pointer with exclusive access
                let map = unsafe { self.map.as_mut() };

                let root =
                    InteriorNode::root(alloc, k, v, map.root.take().unwrap(), n.into_inner())?;
                map.root
                    .replace(ManuallyDrop::new(Node::Interior(ManuallyDrop::into_inner(
                        root.into_inner(),
                    ))));
                map.n += 1;

                Ok(None)
            }
        }
    }
}

impl<'a, 's, A: Allocator, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
    OccupiedEntry<'a, 's, A, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// # Safety
    ///
    /// `alloc` MUST be the allocator that allocated `map`
    pub(crate) unsafe fn new(
        alloc: &'a A,
        inner: OccupiedNodeEntry<'s, K, V, B, MutNodeRef<'s, K, V, B>>,
        map: NonNull<AllocatedBTreeMap<K, V, B>>,
    ) -> Self {
        OccupiedEntry { alloc, inner, map }
    }

    /// Gets a reference to the key in the entry.
    #[must_use]
    pub fn key(&self) -> &K {
        self.inner.key()
    }

    /// Gets a reference to the value in the entry.
    #[must_use]
    pub fn get(&self) -> &V {
        self.inner.get()
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        self.inner.get_mut()
    }

    /// Converts the entry into a mutable reference to its value.
    #[must_use]
    pub fn into_mut(self) -> &'s mut V {
        self.inner.into_mut()
    }

    /// Sets the value of the entry with the `OccupiedEntry`'s key, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        self.inner.insert(value)
    }

    /// Takes the value of the entry out of the map, and returns it.
    #[must_use]
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Takes the key-value pair out of the map, and returns it.
    #[must_use]
    pub fn remove_entry(mut self) -> (K, V) {
        // SAFETY: `self.alloc` was used to create `self.inner`
        let (entry, check_underflow) = unsafe { self.inner.remove(self.alloc) };

        // SAFETY: `self` is `mut`
        unsafe { self.map.as_mut() }.n -= 1;

        if check_underflow {
            // SAFETY: `self` is `mut`
            let map: &mut AllocatedBTreeMap<K, V, B> = unsafe { self.map.as_mut() };
            let root = map.root.as_mut().unwrap();
            if root.n_keys() == 0 {
                let old_root = map.root.take().unwrap();
                let new_root = match ManuallyDrop::into_inner(old_root) {
                    Node::Interior(mut n) => n.take_child_at_in(self.alloc, 0),
                    Node::Leaf(n) => Node::Leaf(n),
                };
                map.root.replace(ManuallyDrop::new(new_root));
            }
        }

        entry
    }
}

impl<'a, 's, A: Allocator, K: core::cmp::PartialOrd + Debug, V, B: ArrayLength>
    Entry<'a, 's, A, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) fn new(
        alloc: &'a A,
        inner: NodeEntry<'s, K, K, V, B, MutNodeRef<'s, K, V, B>>,
        map: NonNull<AllocatedBTreeMap<K, V, B>>,
    ) -> Self {
        match inner {
            NodeEntry::Vacant(inner) => Entry::Vacant(VacantEntry { alloc, inner, map }),
            NodeEntry::Occupied(inner) => Entry::Occupied(OccupiedEntry { alloc, inner, map }),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    #[must_use]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Self::Occupied(mut o) => {
                f(o.get_mut());
                Self::Occupied(o)
            }
            Self::Vacant(v) => Self::Vacant(v),
        }
    }

    /// Returns a reference to this entry's key.
    #[inline]
    pub fn key(&self) -> &K {
        match self {
            Self::Occupied(o) => o.key(),
            Self::Vacant(v) => v.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the provided value if empty,
    /// and returns the old value if the entry was occupied.
    ///
    /// # Errors
    ///
    /// Will return `Err` if the allocation fails.
    pub fn insert(self, v: V) -> AllocResult<Option<V>> {
        match self {
            Self::Occupied(mut o) => Ok(Some(o.insert(v))),
            Self::Vacant(o) => {
                o.insert(v)?;
                Ok(None)
            }
        }
    }

    /// Returns the `OccupiedEntry` if this entry is occupied, panics otherwise.
    pub fn unwrap_occupied(self) -> OccupiedEntry<'a, 's, A, K, V, B> {
        match self {
            Self::Occupied(o) => o,
            Self::Vacant(_) => panic!("Expected Occupied(_)"),
        }
    }
}
