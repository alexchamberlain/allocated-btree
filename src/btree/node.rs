use crate::common::InsertExt;
use crate::common::TakeInsertExt;
use allocated::AllocResult;
use allocated::AllocatorExt;
use allocated::DropIn;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Debug;
use core::ops::Deref;
use generic_array::sequence::GenericSequence;
#[cfg(feature = "std")]
use std::error::Error;
#[cfg(feature = "std")]
use std::io::Write;

#[cfg(feature = "std")]
extern crate alloc;
#[cfg(feature = "std")]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use alloc::format;
use alloc::vec::Vec;

use allocated::DropGuardResult;
use core::mem::ManuallyDrop;
use core::ptr;

use allocator_api2::alloc::Layout;
use core::fmt;
use core::mem::MaybeUninit;
use core::ops::Add;
use core::ops::Mul;
use core::ptr::NonNull;

use allocated::DropGuard;
use allocator_api2::alloc::Allocator;

use generic_array::ArrayLength;
use generic_array::GenericArray;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

mod entry;
mod iter;

#[allow(clippy::module_name_repetitions)]
pub use entry::{NodeEntry, OccupiedNodeEntry, VacantNodeEntry};
pub use iter::{IntoIter, Iter};

type ChildPtr<K, V, B> = Option<NonNull<Node<K, V, B>>>;
type Keys<K, B> = GenericArray<MaybeUninit<K>, Prod<U2, B>>;
type Values<V, B> = GenericArray<MaybeUninit<V>, Prod<U2, B>>;
type Children<K, V, B> = GenericArray<ChildPtr<K, V, B>, Sum<U1, Prod<U2, B>>>;

type DropGuardNode<'a, K, V, B, A> = DropGuard<Node<K, V, B>, &'a A>;

pub struct Node<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    keys: Keys<K, B>,
    values: Values<V, B>,
    children: Children<K, V, B>,
    n_keys: usize,
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> fmt::Debug for Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("keys", &"**UNKNOWN**")
            .field("values", &"**UNKNOWN**")
            .field("children", &self.children)
            .field("n_keys", &self.n_keys)
            .finish()
    }
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn new_in<A: Allocator>(alloc: &A) -> DropGuard<Self, &A> {
        // SAFETY: `alloc` wasn't actually used, so any allocator is safe here.
        unsafe {
            DropGuard::new(
                Node {
                    keys: GenericArray::uninit(),
                    values: GenericArray::uninit(),
                    children: GenericArray::generate(|_| None),
                    n_keys: 0,
                },
                alloc,
            )
        }
    }

    pub fn root<A: Allocator>(
        alloc: &A,
        key: K,
        value: V,
        lhn: ManuallyDrop<Node<K, V, B>>,
        rhn: ManuallyDrop<Node<K, V, B>>,
    ) -> DropGuardResult<Self, &A> {
        let mut keys = GenericArray::uninit();
        keys[0].write(key);

        let mut values = GenericArray::uninit();
        values[0].write(value);

        let lh_heap = alloc.allocate_from(ManuallyDrop::into_inner(lhn))?;
        let rh_heap = alloc.allocate_from(ManuallyDrop::into_inner(rhn))?;

        let mut children: GenericArray<ChildPtr<K, V, B>, _> = GenericArray::generate(|_i| None);
        children[0].replace(lh_heap.into_inner());
        children[1].replace(rh_heap.into_inner());

        // Safety: We used `alloc` above to allocate `lh_heap` and `rh_heap`.
        unsafe {
            Ok(DropGuard::new(
                Node {
                    keys,
                    values,
                    children,
                    n_keys: 1,
                },
                alloc,
            ))
        }
    }

    fn right<'a, A: Allocator>(
        alloc: &'a A,
        keys: &mut [MaybeUninit<K>],
        values: &mut [MaybeUninit<V>],
        first_child: ChildPtr<K, V, B>,
        children: &mut [ChildPtr<K, V, B>],
    ) -> DropGuard<Self, &'a A> {
        assert_eq!(keys.len(), values.len());
        assert_eq!(keys.len(), children.len());

        let new_keys = GenericArray::take(keys);
        let new_values = GenericArray::take(values);
        let new_children = GenericArray::take_and_insert(children, 0, children.len(), first_child);

        // Safety: We used `alloc` above to allocate `lh_heap` and `rh_heap`.
        unsafe {
            DropGuard::new(
                Node {
                    keys: new_keys,
                    values: new_values,
                    children: new_children,
                    n_keys: keys.len(),
                },
                alloc,
            )
        }
    }

    pub fn right_1<'a, A: Allocator>(
        alloc: &'a A,
        key: K,
        value: V,
        rhn: Option<DropGuardNode<'a, K, V, B, A>>,
        keys: &mut [MaybeUninit<K>],
        values: &mut [MaybeUninit<V>],
        children: &mut [ChildPtr<K, V, B>],
    ) -> DropGuardResult<Self, &'a A> {
        assert_eq!(keys.len(), B::to_usize() - 1);
        assert_eq!(keys.len(), values.len());
        assert_eq!(keys.len() + 1, children.len());

        let i = keys
            .iter()
            // Safety: All keys are initialised
            .position(|k| unsafe { *k.assume_init_ref() >= key })
            .unwrap_or(keys.len());

        let new_keys = GenericArray::take_and_insert(keys, i, keys.len(), key);
        let new_values = GenericArray::take_and_insert(values, i, values.len(), value);

        let new_child = if let Some(rhn) = rhn {
            let rh_heap = alloc.allocate_from(ManuallyDrop::into_inner(rhn.into_inner()))?;

            Some(rh_heap.into_inner())
        } else {
            None
        };

        let new_children =
            GenericArray::take_and_insert(children, i + 1, children.len(), new_child);

        // Safety: `alloc` used above to allocate `rh_heap`.
        unsafe {
            Ok(DropGuard::new(
                Node {
                    keys: new_keys,
                    values: new_values,
                    children: new_children,
                    n_keys: B::to_usize(),
                },
                alloc,
            ))
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.children[self.n_keys].is_none()
    }

    pub fn n_keys(&self) -> usize {
        self.n_keys
    }

    pub fn key_at(&self, i: usize) -> &K {
        assert!(i < self.n_keys);
        // Safety: All keys bound by `n_keys` are initialised
        unsafe { self.keys[i].assume_init_ref() }
    }

    pub fn key_at_mut(&mut self, i: usize) -> &mut K {
        assert!(i < self.n_keys);
        // Safety: All keys bound by `n_keys` are initialised; we have a mut ref to self.
        unsafe { self.keys[i].assume_init_mut() }
    }

    pub fn value_at(&self, i: usize) -> &V {
        assert!(i < self.n_keys);
        // Safety: All values bound by `n_keys` are initialised
        unsafe { self.values[i].assume_init_ref() }
    }

    pub fn value_at_mut(&mut self, i: usize) -> &mut V {
        assert!(i < self.n_keys);
        // Safety: All values bound by `n_keys` are initialised; we have a mut ref to self.
        unsafe { self.values[i].assume_init_mut() }
    }

    pub fn key_value_at(&self, i: usize) -> (&K, &V) {
        assert!(i < self.n_keys);
        // SAFETY: Index i < n_keys, so both keys[i] and values[i] are initialized.
        let key = unsafe { self.keys[i].assume_init_ref() };
        // SAFETY: Index i < n_keys, so values[i] is initialized.
        let value = unsafe { self.values[i].assume_init_ref() };
        (key, value)
    }

    pub fn key_value_mut_at(&mut self, i: usize) -> (&K, &mut V) {
        assert!(i < self.n_keys);
        // SAFETY: Index i < n_keys, so both keys[i] and values[i] are initialized.
        let key = unsafe { self.keys[i].assume_init_ref() };
        // SAFETY: Index i < n_keys, so values[i] is initialized. Mutable reference is exclusive.
        let value = unsafe { self.values[i].assume_init_mut() };
        (key, value)
    }

    pub fn take_key_value_at(&mut self, i: usize) -> (K, V) {
        assert!(i < self.n_keys);
        // SAFETY: Index i < n_keys, so both keys[i] and values[i] are initialized.
        let key = unsafe { self.keys[i].assume_init_read() };
        // SAFETY: Index i < n_keys, so values[i] is initialized. Takes ownership.
        let value = unsafe { self.values[i].assume_init_read() };
        (key, value)
    }

    pub fn child_at(&self, i: usize) -> Option<&NonNull<Node<K, V, B>>> {
        assert!(i <= self.n_keys);
        self.children[i].as_ref()
    }

    fn interior_child_at_mut(&mut self, i: usize) -> &mut Node<K, V, B> {
        assert!(i <= self.n_keys);
        // SAFETY: Requires children[i] is Some and points to a valid, uniquely-owned Node.
        unsafe { self.children[i].as_mut().unwrap().as_mut() }
    }

    pub fn take_child_at_in<A: Allocator>(&mut self, alloc: &A, i: usize) -> Node<K, V, B> {
        assert!(i <= self.n_keys);
        let mut child_ptr = self.children[i].take().unwrap();

        // SAFETY: child_ptr is valid and uniquely owned by this node.
        let child_ref = unsafe { child_ptr.as_mut() };
        // SAFETY: We're taking ownership of the child, which will not be accessed again.
        let child = unsafe { core::ptr::read(child_ref) };

        // SAFETY: child_ptr was allocated with this allocator and is no longer needed.
        unsafe {
            alloc.deallocate(child_ptr.cast(), Layout::new::<Node<K, V, B>>());
        }

        child
    }

    /// # Safety
    ///
    /// `parents` MUST be the ancestors of this node.
    pub unsafe fn entry_in(
        &mut self,
        key: K,
        mut parents: Vec<(*mut Self, usize)>,
    ) -> NodeEntry<'_, K, K, V, B, &mut Node<K, V, B>>
    where
        K: Debug,
    {
        let (i, match_) = self.find(&key);

        if match_ {
            return NodeEntry::Occupied(OccupiedNodeEntry::new(parents, self, i));
        }

        parents.push((self, i));
        let child = self.children[i];

        match child {
            None => {
                let parents = parents.into_iter().map(|(n, _)| n).collect();
                NodeEntry::Vacant(VacantNodeEntry::new(key, parents, i))
            }
            Some(mut child) => {
                // SAFETY: child pointer is valid and uniquely owned.
                let child_ref = unsafe { child.as_mut() };
                // SAFETY: parents contains valid ancestors.
                unsafe { child_ref.entry_in(key, parents) }
            }
        }
    }

    fn find<Q>(&self, search_key: &Q) -> (usize, bool)
    where
        K: Borrow<Q> + PartialOrd,
        Q: PartialOrd + ?Sized + core::fmt::Debug,
    {
        for i in 0..self.n_keys {
            match self.key_at(i).borrow().partial_cmp(search_key) {
                Some(Ordering::Less) => continue,
                Some(Ordering::Greater) => {
                    return (i, false);
                }
                _ => {
                    return (i, true);
                }
            }
        }

        (self.n_keys, false)
    }

    /// # Errors
    ///
    /// Will return `Err` if the allocation fails.
    ///
    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate `self`.
    unsafe fn insert_in_here<'a, 's, A: Allocator>(
        &'s mut self,
        alloc: &'a A,
        key: K,
        value: V,
        i: usize,
        rhn: Option<DropGuardNode<'a, K, V, B, A>>,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let b = B::to_usize();
        if self.n_keys == b * 2 {
            let old_median = self.key_at(b);
            if key < *old_median {
                if i == b {
                    let rhn = if let Some(rhn) = rhn {
                        let rh_heap =
                            alloc.allocate_from(ManuallyDrop::into_inner(rhn.into_inner()))?;
                        Some(rh_heap.into_inner())
                    } else {
                        None
                    };
                    let new_rhn = Self::right(
                        alloc,
                        &mut self.keys[b..],
                        &mut self.values[b..],
                        rhn,
                        &mut self.children[b + 1..],
                    );

                    self.n_keys = b;
                    assert_eq!(new_rhn.n_keys, b);
                    Ok(InsertOption::Split((key, value, new_rhn)))
                } else {
                    let new_rhn = Self::right(
                        alloc,
                        &mut self.keys[b..],
                        &mut self.values[b..],
                        self.children[b],
                        &mut self.children[b + 1..],
                    );
                    let (median_key, median_value) = self.take_key_value_at(b - 1);
                    self.n_keys = b - 1;

                    // SAFETY: alloc is passed through from caller, maintaining allocator matching
                    let r = unsafe { self.insert_in_here(alloc, key, value, i, rhn)? };
                    assert!(r.is_new_key());
                    assert_eq!(self.n_keys, b);
                    assert_eq!(new_rhn.n_keys, b);

                    Ok(InsertOption::Split((median_key, median_value, new_rhn)))
                }
            } else {
                let rhn = Self::right_1(
                    alloc,
                    key,
                    value,
                    rhn,
                    &mut self.keys[b + 1..],
                    &mut self.values[b + 1..],
                    &mut self.children[b + 1..],
                )?;

                let (median_key, median_value) = self.take_key_value_at(b);
                self.n_keys = b;

                Ok(InsertOption::Split((median_key, median_value, rhn)))
            }
        } else {
            assert!(self.n_keys >= i);

            let child = if let Some(rhn) = rhn {
                let rh_heap = alloc.allocate_from(ManuallyDrop::into_inner(rhn.into_inner()))?;
                Some(rh_heap.into_inner())
            } else {
                None
            };

            self.keys.insert(i, self.n_keys, key);
            self.values.insert(i, self.n_keys, value);
            self.children.insert(i + 1, self.n_keys + 1, child);

            self.n_keys += 1;

            Ok(InsertOption::NewKey(self.value_at_mut(i)))
        }
    }

    fn _insert_first_entry(&mut self, entry: (K, V), child: ChildPtr<K, V, B>) {
        if self.n_keys > 0 {
            assert!(&entry.0 < self.key_at(0));
        }

        self.keys.insert(0, self.n_keys, entry.0);
        self.values.insert(0, self.n_keys, entry.1);
        self.children.insert(0, self.n_keys + 1, child);

        self.n_keys += 1;
    }

    fn _insert_last_entry(&mut self, entry: (K, V), child: ChildPtr<K, V, B>) {
        if self.n_keys > 0 {
            let i = self.n_keys - 1;
            assert!(self.key_at(i) < &entry.0);
        }

        self.keys[self.n_keys].write(entry.0);
        self.values[self.n_keys].write(entry.1);
        self.children[self.n_keys + 1] = child;

        self.n_keys += 1;
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this B-tree and its nodes.
    unsafe fn remove_from_here_in<A: Allocator>(&mut self, alloc: &A, i: usize) -> (K, V) {
        if self.children[i + 1].is_none() {
            return self.remove_leaf(i);
        }

        let entry = self.take_key_value_at(i);

        let child = self.children[i + 1].as_mut().unwrap();
        // SAFETY: Requires children[i+1] points to a valid, uniquely-owned Node.
        let child = unsafe { child.as_mut() };
        // SAFETY: alloc is passed through from caller, maintaining allocator matching
        let (k, v) = unsafe { child.remove_first_child(alloc) };
        self.keys[i].write(k);
        self.values[i].write(v);

        self.check_underflow(alloc, i + 1);

        entry
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate this object.
    unsafe fn remove_first_child<A: Allocator>(&mut self, alloc: &A) -> (K, V) {
        match self.children[0].as_mut() {
            Some(child) => {
                // SAFETY: child pointer is valid and uniquely owned.
                let child_ref = unsafe { child.as_mut() };
                // SAFETY: alloc is the same allocator used for the B-tree.
                let entry = unsafe { child_ref.remove_first_child(alloc) };
                self.check_underflow(alloc, 0);
                entry
            }
            None => self.remove_leaf(0),
        }
    }

    fn _take_first_child(&mut self) -> ((K, V), ChildPtr<K, V, B>) {
        let key = self.keys.pop_at(0, self.n_keys);
        let value = self.values.pop_at(0, self.n_keys);
        let child = self.children.pop_at(0, self.n_keys + 1);
        self.n_keys -= 1;

        ((key, value), child)
    }

    fn _take_last_child(&mut self) -> ((K, V), ChildPtr<K, V, B>) {
        let entry = self.take_key_value_at(self.n_keys - 1);
        let child = self.children[self.n_keys].take();
        self.n_keys -= 1;

        (entry, child)
    }

    #[inline]
    fn check_underflow<A: Allocator>(&mut self, alloc: &A, mut i: usize) -> bool {
        assert!(self.children[i].is_some());

        // SAFETY: Requires children[i] points to a valid, uniquely-owned Node.
        let child = unsafe { self.children[i].as_mut().unwrap().as_mut() };
        assert!(child.n_keys >= B::to_usize() - 1);

        if child.n_keys != B::to_usize() - 1 {
            return false;
        }

        if i != 0 {
            // SAFETY: Requires children[i-1] points to a valid, uniquely-owned Node.
            let lhs = unsafe { self.children[i - 1].as_mut().unwrap().as_mut() };
            if lhs.n_keys > B::to_usize() {
                // Borrow an entry from the lhs
                let (entry, lhs_child) = lhs._take_last_child();
                let entry = self._replace_entry(i - 1, entry);
                child._insert_first_entry(entry, lhs_child);

                return false;
            }
        }

        if i != self.n_keys {
            // SAFETY: Requires children[i+1] points to a valid, uniquely-owned Node.
            let rhs = unsafe { self.children[i + 1].as_mut().unwrap().as_mut() };
            if rhs.n_keys > B::to_usize() {
                // Borrow an entry from the rhs
                let (entry, rhs_child) = rhs._take_first_child();
                let entry = self._replace_entry(i, entry);
                child._insert_last_entry(entry, rhs_child);

                return false;
            }
        }

        // Merge
        if i == 0 {
            i = 1;
        }

        let key = self.keys.pop_at(i - 1, self.n_keys);
        let value = self.values.pop_at(i - 1, self.n_keys);
        let mut child_ptr = self.children.pop_at(i, self.n_keys + 1).unwrap();

        // SAFETY: child_ptr is valid and uniquely owned by this node.
        let child_ref = unsafe { child_ptr.as_mut() };
        // SAFETY: We're taking ownership of the child, which will not be accessed again.
        let child = unsafe { core::ptr::read(child_ref) };

        // SAFETY: child_ptr was allocated with this allocator and is no longer needed.
        unsafe {
            alloc.deallocate(child_ptr.cast(), Layout::new::<Node<K, V, B>>());
        }

        self.interior_child_at_mut(i - 1)
            ._merge((key, value), child);

        self.n_keys -= 1;

        true
    }

    fn _merge(&mut self, pair: (K, V), mut rhs: Node<K, V, B>) {
        assert!(self.n_keys + rhs.n_keys + 1 == B::to_usize() * 2);

        self._write_pair(self.n_keys, pair);
        self.n_keys += 1;

        // SAFETY: Copy keys from rhs to self. Pointers are valid and non-overlapping.
        let src = rhs.keys.as_mut_ptr();
        // SAFETY: self.n_keys <= 2*B after pair insertion, so offset is within bounds
        let dst = unsafe { self.keys.as_mut_ptr().add(self.n_keys) };
        // SAFETY: src and dst are valid, non-overlapping pointers within their respective arrays
        unsafe {
            ptr::copy(src, dst, rhs.n_keys);
        }
        // SAFETY: Copy values from rhs to self. Pointers are valid and non-overlapping.
        let src = rhs.values.as_mut_ptr();
        // SAFETY: self.n_keys <= 2*B, so offset is within bounds
        let dst = unsafe { self.values.as_mut_ptr().add(self.n_keys) };
        // SAFETY: src and dst are valid, non-overlapping pointers within their respective arrays
        unsafe {
            ptr::copy(src, dst, rhs.n_keys);
        }

        // Copy all rhs.n_keys + 1 children from rhs (one more child than keys)
        // But only if this is an interior node (children exist)
        if rhs.children[0].is_some() {
            // Interior node - copy all children
            for j in 0..=rhs.n_keys {
                self.children[self.n_keys + j] = rhs.children[j].take();
            }
        } else {
            // Leaf node - no children to copy, but ensure they're all None
            for j in 0..=self.n_keys + rhs.n_keys {
                self.children[j] = None;
            }
        }

        self.n_keys += rhs.n_keys;

        assert_eq!(self.n_keys, B::to_usize() * 2);
    }

    fn _replace_entry(&mut self, i: usize, pair: (K, V)) -> (K, V) {
        let entry = self.take_key_value_at(i);
        self._write_pair(i, pair);
        entry
    }

    fn _write_pair(&mut self, i: usize, pair: (K, V)) {
        self.keys[i].write(pair.0);
        self.values[i].write(pair.1);
    }

    #[inline]
    fn remove_leaf(&mut self, i: usize) -> (K, V) {
        assert!(i < self.n_keys);
        let entry = self.take_key_value_at(i);

        // SAFETY: Shift keys left to fill the gap. Elements [i+1..n_keys) → [i..n_keys-1).
        // SAFETY: i + 1 <= n_keys, so offset is within bounds
        let src = unsafe { self.keys.as_mut_ptr().add(i + 1) };
        // SAFETY: i < n_keys, so offset is within bounds
        let dst = unsafe { self.keys.as_mut_ptr().add(i) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }
        // SAFETY: Shift values left to fill the gap. Elements [i+1..n_keys) → [i..n_keys-1).
        // SAFETY: i + 1 <= n_keys, so offset is within bounds
        let src = unsafe { self.values.as_mut_ptr().add(i + 1) };
        // SAFETY: i < n_keys, so offset is within bounds
        let dst = unsafe { self.values.as_mut_ptr().add(i) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }
        // SAFETY: Shift children left. Elements [i+2..n_keys+1) → [i+1..n_keys).
        // SAFETY: i + 2 <= n_keys + 1 <= capacity, so offset is within bounds
        let src = unsafe { self.children.as_mut_ptr().add(i + 2) };
        // SAFETY: i + 1 <= n_keys < capacity, so offset is within bounds
        let dst = unsafe { self.children.as_mut_ptr().add(i + 1) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }

        self.n_keys -= 1;
        entry
    }
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> DropIn for Node<K, V, B>
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
        for i in 0..=self.n_keys {
            if let Some(mut ptr) = self.children[i] {
                // SAFETY: ptr is valid and uniquely owned.
                let child = unsafe { ptr.as_mut() };
                // SAFETY: alloc is the same allocator used for the B-tree.
                unsafe { child.drop_in(alloc) };
                // SAFETY: ptr was allocated with this allocator and child is dropped.
                unsafe {
                    alloc.deallocate(ptr.cast(), Layout::new::<Node<K, V, B>>());
                }
            }
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

#[allow(clippy::module_name_repetitions)]
pub trait NodeRef<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>:
    Deref<Target = Node<K, V, B>> + Sized + Debug
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Ptr: Debug;
    type ValueRef: 'n + Deref<Target = V>;

    /// # Safety
    ///
    /// Caller is responsibility for matching mutability.
    unsafe fn from_ptr(p: Self::Ptr) -> Self;

    /// # Safety
    ///
    /// Caller is responsibility for matching mutability.
    unsafe fn from_non_null(p: NonNull<Node<K, V, B>>) -> Self;

    fn as_ptr(&mut self) -> Self::Ptr;

    fn into_value_at(self, i: usize) -> &'n V;
    fn into_key_value_at(self, i: usize) -> (&'n K, Self::ValueRef);
    fn into_child_at(self, i: usize) -> Option<Self>;

    fn first_entry(
        mut self,
        mut parents: Vec<(Self::Ptr, usize)>,
    ) -> OccupiedNodeEntry<'n, K, V, B, Self>
    where
        Self: Sized,
    {
        if self.is_leaf() {
            OccupiedNodeEntry::new(parents, self, 0)
        } else {
            parents.push((self.as_ptr(), 0));
            self.into_child_at(0).unwrap().first_entry(parents)
        }
    }

    fn ref_entry<'s, Q>(
        mut self,
        key: &'s Q,
        mut parents: Vec<(Self::Ptr, usize)>,
    ) -> NodeEntry<'n, K, &'s Q, V, B, Self>
    where
        K: Borrow<Q> + core::cmp::PartialOrd,
        Q: core::cmp::PartialOrd + Debug,
    {
        let (i, match_) = self.find(key);

        if match_ {
            return NodeEntry::Occupied(OccupiedNodeEntry::new(parents, self, i));
        }

        parents.push((self.as_ptr(), i));
        let child = self.into_child_at(i);

        match child {
            None => {
                let parents = parents.into_iter().map(|(p, _)| p).collect();
                NodeEntry::Vacant(VacantNodeEntry::new(key, parents, i))
            }
            Some(child) => child.ref_entry(key, parents),
        }
    }
}

impl<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeRef<'n, K, V, B>
    for &'n Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Ptr = *const Node<K, V, B>;
    type ValueRef = &'n V;

    unsafe fn from_ptr(p: *const Node<K, V, B>) -> Self {
        // SAFETY: Requires p is a valid pointer with lifetime 'n
        unsafe { &*p }
    }

    unsafe fn from_non_null(p: NonNull<Node<K, V, B>>) -> Self {
        // SAFETY: Requires p points to valid Node with lifetime 'n
        unsafe { p.as_ref() }
    }

    fn as_ptr(&mut self) -> Self::Ptr {
        *self
    }

    fn into_value_at(self, i: usize) -> &'n V {
        Node::value_at(self, i)
    }

    fn into_key_value_at(self, i: usize) -> (&'n K, &'n V) {
        Node::key_value_at(self, i)
    }

    fn into_child_at(self, i: usize) -> Option<Self> {
        // SAFETY: Requires p points to valid Node with lifetime matching self
        self.children[i].as_ref().map(|p| unsafe { p.as_ref() })
    }
}

impl<'n, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> NodeRef<'n, K, V, B>
    for &'n mut Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Ptr = *mut Node<K, V, B>;
    type ValueRef = &'n mut V;

    unsafe fn from_ptr(p: *mut Node<K, V, B>) -> Self {
        // SAFETY: Requires p is a valid, uniquely-owned pointer with lifetime 'n
        unsafe { &mut *p }
    }

    unsafe fn from_non_null(mut p: NonNull<Node<K, V, B>>) -> Self {
        // SAFETY: Requires p points to valid, uniquely-owned Node with lifetime 'n
        unsafe { p.as_mut() }
    }

    fn as_ptr(&mut self) -> Self::Ptr {
        *self
    }

    fn into_value_at(self, i: usize) -> &'n V {
        Node::value_at(self, i)
    }

    fn into_key_value_at(self, i: usize) -> (&'n K, &'n mut V) {
        Node::key_value_mut_at(self, i)
    }

    fn into_child_at(self, i: usize) -> Option<Self> {
        // SAFETY: Requires p points to valid, uniquely-owned Node with lifetime matching self
        self.children[i].as_mut().map(|p| unsafe { p.as_mut() })
    }

    // fn as_ref(&self) -> &'n Node<K, V, B> { self }
}

#[cfg(feature = "std")]
impl<K: core::cmp::PartialOrd + Debug, V: Debug, B: ArrayLength> Node<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub fn to_dot(&self, data: &mut Vec<u8>) -> Result<(), Box<dyn Error>> {
        let this = core::ptr::from_ref(self);
        data.write_all(
            format!(
                "\"p{:?}\" [shape=\"record\"; label=\"{:?} ({})|{{",
                this, this, self.n_keys
            )
            .as_bytes(),
        )?;

        if self.n_keys == 0 {
            data.write_all(b"}\"];\n")?;
        }

        for i in 0..self.n_keys {
            // SAFETY: i < n_keys, so keys[i] is initialized
            let key = unsafe { self.keys[i].assume_init_ref() };
            data.write_all(format!("{key:?}").as_bytes())?;

            if i != self.n_keys - 1 {
                data.write_all(b"|")?;
            } else {
                data.write_all(b"}|{")?;
            }
        }
        for i in 0..self.n_keys {
            // SAFETY: i < n_keys, so values[i] is initialized
            let value = unsafe { self.values[i].assume_init_ref() };
            data.write_all(format!("{value:?}").as_bytes())?;

            if i != self.n_keys - 1 {
                data.write_all(b"|")?;
            } else {
                data.write_all(b"}\"];\n")?;
            }
        }

        for i in 0..=self.n_keys {
            let child = self.children[i].as_ref();
            if let Some(child) = child {
                // SAFETY: Requires child points to a valid Node
                let that = unsafe { child.as_ref() };
                data.write_all(
                    format!("\"p{:?}\" -> \"p{:?}\";\n", this, core::ptr::from_ref(that))
                        .as_bytes(),
                )?;

                that.to_dot(data)?;
            }
        }

        Ok(())
    }
}
