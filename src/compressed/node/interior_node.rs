use crate::common::InsertExt;
use crate::common::TakeInsertExt;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
#[cfg(feature = "std")]
use core::fmt::Debug;
use core::mem::ManuallyDrop;
use core::mem::MaybeUninit;
use core::ops::Add;
use core::ops::Mul;
use core::ptr;
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

use allocated::AllocResult;
use allocated::DropGuard;
use allocated::DropGuardResult;
use allocated::DropIn;
use allocator_api2::alloc::Allocator;
use generic_array::sequence::GenericSequence;
use generic_array::ArrayLength;
use generic_array::GenericArray;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use super::child_ptr::ChildPtr;
use super::node_ref::NodeRefT;
use super::DropGuardNode;
use super::InsertOption;
use super::MutNodeRef;
use super::Node;
use super::NodeEntry;
use super::NodeRef;
use super::OccupiedNodeEntry;
use super::VacantNodeEntry;

type Keys<K, B> = GenericArray<MaybeUninit<K>, Prod<U2, B>>;
type Values<V, B> = GenericArray<MaybeUninit<V>, Prod<U2, B>>;
type Children<B> = GenericArray<ChildPtr, Sum<U1, Prod<U2, B>>>;

pub struct InteriorNode<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    keys: Keys<K, B>,
    values: Values<V, B>,
    children: Children<B>,
    n_keys: usize,
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> fmt::Debug
    for InteriorNode<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InteriorNode")
            .field("keys", &"**UNKNOWN**")
            .field("values", &"**UNKNOWN**")
            .field("children", &self.children)
            .field("n_keys", &self.n_keys)
            .finish()
    }
}
impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> InteriorNode<K, V, B>
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
                InteriorNode {
                    keys: GenericArray::uninit(),
                    values: GenericArray::uninit(),
                    children: GenericArray::generate(|_| ChildPtr::null()),
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

        let mut children: GenericArray<ChildPtr, _> = GenericArray::generate(|_i| ChildPtr::null());
        children[0].replace(ChildPtr::from_node_in(
            alloc,
            ManuallyDrop::into_inner(lhn),
        )?);
        children[1].replace(ChildPtr::from_node_in(
            alloc,
            ManuallyDrop::into_inner(rhn),
        )?);

        // SAFETY: All fields are properly initialized: keys/values arrays, children pointers, n_keys=1
        Ok(unsafe {
            DropGuard::new(
                InteriorNode {
                    keys,
                    values,
                    children,
                    n_keys: 1,
                },
                alloc,
            )
        })
    }

    pub fn right<'a, A: Allocator>(
        alloc: &'a A,
        keys: &mut [MaybeUninit<K>],
        values: &mut [MaybeUninit<V>],
        first_child: ChildPtr,
        children: &mut [ChildPtr],
    ) -> DropGuard<Node<K, V, B>, &'a A> {
        assert_eq!(keys.len(), values.len());
        assert_eq!(keys.len(), children.len());
        let mut new_keys = GenericArray::uninit();
        // SAFETY: Copying MaybeUninit data from keys slice to new_keys array
        unsafe {
            ptr::copy(keys.as_mut_ptr(), new_keys.as_mut_ptr(), keys.len());
        }
        let mut new_values = GenericArray::uninit();
        // SAFETY: Copying MaybeUninit data from values slice to new_values array
        unsafe {
            ptr::copy(values.as_mut_ptr(), new_values.as_mut_ptr(), values.len());
        }

        let new_children = GenericArray::generate(|i| {
            if i == 0 {
                first_child
            } else if i - 1 < children.len() {
                children[i - 1]
            } else {
                ChildPtr::null()
            }
        });

        // SAFETY: The allocator is valid and matches the one used for allocation
        unsafe {
            DropGuard::new(
                Node::Interior(InteriorNode {
                    keys: new_keys,
                    values: new_values,
                    children: new_children,
                    n_keys: keys.len(),
                }),
                alloc,
            )
        }
    }

    pub fn right_1<'a, A: Allocator>(
        alloc: &'a A,
        key: K,
        value: V,
        rhn: DropGuardNode<'a, K, V, B, A>,
        keys: &mut [MaybeUninit<K>],
        values: &mut [MaybeUninit<V>],
        children: &mut [ChildPtr],
    ) -> DropGuardResult<Node<K, V, B>, &'a A> {
        assert_eq!(keys.len(), B::to_usize() - 1);
        assert_eq!(keys.len(), values.len());
        assert_eq!(keys.len() + 1, children.len());

        let i = keys
            .iter()
            // SAFETY: We're only reading from initialized keys in the slice
            .position(|k| unsafe { *k.assume_init_ref() >= key })
            .unwrap_or(keys.len());

        let new_keys = GenericArray::take_and_insert(keys, i, keys.len(), key);
        let new_values = GenericArray::take_and_insert(values, i, values.len(), value);
        let new_children = GenericArray::take_and_insert(
            children,
            i + 1,
            children.len(),
            ChildPtr::from_node_in(alloc, ManuallyDrop::into_inner(rhn.into_inner()))?,
        );

        // SAFETY: The allocator is valid and matches the one used for allocation
        Ok(unsafe {
            DropGuard::new(
                Node::Interior(InteriorNode {
                    keys: new_keys,
                    values: new_values,
                    children: new_children,
                    n_keys: B::to_usize(),
                }),
                alloc,
            )
        })
    }

    pub fn is_leaf(&self) -> bool {
        // self.children[self.n_keys].is_none()
        false
    }

    pub fn n_keys(&self) -> usize {
        self.n_keys
    }

    pub fn key_at(&self, i: usize) -> &K {
        assert!(i < self.n_keys);
        // SAFETY: i < n_keys, so keys[i] is initialized
        unsafe { self.keys[i].assume_init_ref() }
    }

    pub fn key_at_mut(&mut self, i: usize) -> &mut K {
        assert!(i < self.n_keys);
        // SAFETY: i < n_keys, so keys[i] is initialized. Mutable access is exclusive.
        unsafe { self.keys[i].assume_init_mut() }
    }

    pub fn value_at(&self, i: usize) -> &V {
        assert!(i < self.n_keys);
        // SAFETY: i < n_keys, so values[i] is initialized
        unsafe { self.values[i].assume_init_ref() }
    }

    pub fn value_at_mut(&mut self, i: usize) -> &mut V {
        assert!(i < self.n_keys);
        // SAFETY: i < n_keys, so values[i] is initialized. Mutable access is exclusive.
        unsafe { self.values[i].assume_init_mut() }
    }

    pub fn key_value_at(&self, i: usize) -> (&K, &V) {
        assert!(i < self.n_keys);
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let key = unsafe { self.keys[i].assume_init_ref() };
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let value = unsafe { self.values[i].assume_init_ref() };
        (key, value)
    }

    pub fn key_value_mut_at(&mut self, i: usize) -> (&K, &mut V) {
        assert!(i < self.n_keys);
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let key = unsafe { self.keys[i].assume_init_ref() };
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let value = unsafe { self.values[i].assume_init_mut() };
        (key, value)
    }

    pub fn take_key_value_at(&mut self, i: usize) -> (K, V) {
        assert!(i < self.n_keys);
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let key = unsafe { self.keys[i].assume_init_read() };
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let value = unsafe { self.values[i].assume_init_read() };
        (key, value)
    }

    pub fn child_at(&self, i: usize) -> Option<NodeRef<'_, K, V, B>> {
        assert!(i <= self.n_keys);
        self.children[i].as_option_node_ref()
    }

    pub fn child_at_mut(&mut self, i: usize) -> Option<MutNodeRef<'_, K, V, B>> {
        assert!(i <= self.n_keys);
        self.children[i].as_option_mut_node_ref()
    }

    fn interior_child_at_mut(&mut self, i: usize) -> &mut InteriorNode<K, V, B> {
        assert!(i <= self.n_keys);
        // SAFETY: Requires children[i] points to a valid InteriorNode (not a LeafNode)
        unsafe { self.children[i].as_mut_interior_node() }
    }

    pub fn take_child_at_in<A: Allocator>(&mut self, alloc: &A, i: usize) -> Node<K, V, B> {
        assert!(i <= self.n_keys);
        let child_ptr = self.children[i];
        // SAFETY: alloc matches the allocator used to create this child_ptr
        unsafe { child_ptr.read_and_deallocate_in(alloc) }
    }

    /// # Safety
    ///
    /// `parents` MUST be the parents of this node.
    pub unsafe fn entry_in(
        &mut self,
        key: K,
        mut parents: Vec<(ChildPtr, usize)>,
    ) -> NodeEntry<'_, K, K, V, B, MutNodeRef<'_, K, V, B>> {
        let (i, match_) = self.find(&key);

        if match_ {
            return NodeEntry::Occupied(OccupiedNodeEntry::new(
                parents,
                MutNodeRef::Interior(self),
                i,
            ));
        }

        let child = self.children[i];

        match child.as_option_mut_node_ref() {
            None => {
                // Child doesn't exist - create vacant entry at this interior node
                NodeEntry::Vacant(VacantNodeEntry::new(
                    key,
                    parents,
                    MutNodeRef::Interior(self),
                    i,
                ))
            }
            // SAFETY: Requires child is a valid node reference with correct lifetime and parents list
            Some(child) => {
                parents.push((ChildPtr::from_interior_node(self.into()), i));
                unsafe { child.entry_in(key, parents) }
            }
        }
    }

    pub fn find<Q>(&self, search_key: &Q) -> (usize, bool)
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
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn insert_in_here<'a, 's, A: Allocator>(
        &'s mut self,
        alloc: &'a A,
        key: K,
        value: V,
        i: usize,
        rhn: DropGuardNode<'a, K, V, B, A>,
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let b = B::to_usize();
        if self.n_keys == b * 2 {
            // SAFETY: n_keys == 2*B, so b < n_keys, therefore keys[b] is initialized
            let old_median = unsafe { self.keys[b].assume_init_ref() };
            if key < *old_median {
                if i == b {
                    let rhn =
                        ChildPtr::from_node_in(alloc, ManuallyDrop::into_inner(rhn.into_inner()))?;
                    let new_rhn = Self::right(
                        alloc,
                        &mut self.keys[b..],
                        &mut self.values[b..],
                        rhn,
                        &mut self.children[b + 1..],
                    );

                    self.n_keys = b;
                    // assert_eq!(self.n_keys, b);
                    assert_eq!(new_rhn.n_keys(), b);

                    Ok(InsertOption::Split((key, value, new_rhn)))
                } else {
                    let new_rhn = Self::right(
                        alloc,
                        &mut self.keys[b..],
                        &mut self.values[b..],
                        self.children[b],
                        &mut self.children[b + 1..],
                    );
                    // SAFETY: b-1 < b <= n_keys, so keys[b-1] is initialized. Takes ownership.
                    let median_key = unsafe { self.keys[b - 1].assume_init_read() };
                    // SAFETY: b-1 < n_keys, so values[b-1] is initialized. Takes ownership.
                    let median_value = unsafe { self.values[b - 1].assume_init_read() };
                    self.n_keys = b - 1;

                    // SAFETY: alloc is passed through from caller, maintaining allocator matching
                    let r = unsafe { self.insert_in_here(alloc, key, value, i, rhn)? };
                    assert!(r.is_new_key());
                    assert_eq!(self.n_keys, b);
                    assert_eq!(new_rhn.n_keys(), b);

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
                self.n_keys = b;
                Ok(InsertOption::Split((
                    // SAFETY: b < original n_keys (2*B), so keys[b] is initialized. Takes ownership.
                    unsafe { self.keys[b].assume_init_read() },
                    // SAFETY: b < original n_keys (2*B), so values[b] is initialized. Takes ownership.
                    unsafe { self.values[b].assume_init_read() },
                    rhn,
                )))
            }
        } else {
            assert!(self.n_keys >= i);

            self.keys.insert(i, self.n_keys, key);
            self.values.insert(i, self.n_keys, value);
            self.children.insert(
                i + 1,
                self.n_keys + 1,
                ChildPtr::from_node_in(alloc, ManuallyDrop::into_inner(rhn.into_inner()))?,
            );

            self.n_keys += 1;

            // SAFETY: values[i] was just initialized via insert(), and i < n_keys
            Ok(InsertOption::NewKey(unsafe {
                self.values[i].assume_init_mut()
            }))
        }
    }

    pub fn insert_first_entry(&mut self, entry: (K, V), child: ChildPtr) {
        if self.n_keys > 0 {
            // SAFETY: n_keys > 0, so keys[0] is initialized
            assert!(&entry.0 < unsafe { self.keys[0].assume_init_ref() });

            // SAFETY: Copying keys from index 0 to 1, shifting right to make room
            // SAFETY: Offset 0 is always valid (start of array)
            let src = unsafe { self.keys.as_mut_ptr().add(0) };
            // SAFETY: Offset 1 is valid (n_keys < 2*B, so capacity > 1)
            let dst = unsafe { self.keys.as_mut_ptr().add(1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys);
            }
            // SAFETY: Copying values from index 0 to 1, shifting right to make room
            // SAFETY: Offset 0 is always valid
            let src = unsafe { self.values.as_mut_ptr().add(0) };
            // SAFETY: Offset 1 is valid (same bounds as keys)
            let dst = unsafe { self.values.as_mut_ptr().add(1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys);
            }

            // SAFETY: Copying children from index 0 to 1, shifting right to make room
            // SAFETY: Offset 0 is always valid
            let src = unsafe { self.children.as_mut_ptr().add(0) };
            // SAFETY: Offset 1 is valid (children capacity is 2*B+1)
            let dst = unsafe { self.children.as_mut_ptr().add(1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys + 1);
            }
        }

        self.keys[0].write(entry.0);
        self.values[0].write(entry.1);
        self.children[0] = child;

        self.n_keys += 1;
    }

    pub fn insert_last_entry(&mut self, entry: (K, V), child: ChildPtr) {
        self._insert_last_entry(entry, child);
    }

    fn _insert_last_entry(&mut self, entry: (K, V), child: ChildPtr) {
        // unsafe { std::intrinsics::breakpoint(); }

        if self.n_keys > 0 {
            let i = self.n_keys - 1;
            // SAFETY: i = n_keys-1, and n_keys > 0, so i < n_keys and keys[i] is initialized
            assert!(unsafe { self.keys[i].assume_init_ref() } < &entry.0);
        }

        self.keys[self.n_keys].write(entry.0);
        self.values[self.n_keys].write(entry.1);
        self.children[self.n_keys + 1] = child;

        self.n_keys += 1;
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn remove_first_child<A: Allocator>(&mut self, alloc: &A) -> (K, V) {
        let mut child = self.children[0].as_mut_node_ref();
        // SAFETY: alloc matches the allocator used for child
        let entry = unsafe { child.remove_first_child(alloc) };
        self.check_underflow(alloc, 0);
        entry
    }

    pub fn take_first_child(&mut self) -> ((K, V), ChildPtr) {
        let entry = self.take_key_value_at(0);
        let child = self.children[0].take();
        self.n_keys -= 1;

        // SAFETY: Copying keys from index 1 to 0, shifting left after removal
        // SAFETY: Offset 1 is valid (original n_keys > 0)
        let src = unsafe { self.keys.as_mut_ptr().add(1) };
        // SAFETY: Offset 0 is always valid (start of array)
        let dst = unsafe { self.keys.as_mut_ptr().add(0) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys);
        }

        // SAFETY: Copying values from index 1 to 0, shifting left after removal
        // SAFETY: Offset 1 is valid (original n_keys > 0)
        let src = unsafe { self.values.as_mut_ptr().add(1) };
        // SAFETY: Offset 0 is always valid
        let dst = unsafe { self.values.as_mut_ptr().add(0) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys);
        }

        // SAFETY: Copying children from index 1 to 0, shifting left after removal
        // SAFETY: Offset 1 is valid (children array size is 2*B+1)
        let src = unsafe { self.children.as_mut_ptr().add(1) };
        // SAFETY: Offset 0 is always valid
        let dst = unsafe { self.children.as_mut_ptr().add(0) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys + 1);
        }

        (entry, child)
    }

    pub fn merge(&mut self, pair: (K, V), mut rhs: InteriorNode<K, V, B>) {
        assert!(self.n_keys + rhs.n_keys + 1 == B::to_usize() * 2);

        self._write_pair(self.n_keys, pair);
        self.n_keys += 1;

        // SAFETY: Copying keys from rhs to self at the appropriate position
        let src = rhs.keys.as_mut_ptr();
        // SAFETY: self.n_keys + 1 + rhs.n_keys = 2*B, so offset is within bounds
        let dst = unsafe { self.keys.as_mut_ptr().add(self.n_keys) };
        // SAFETY: src and dst are valid, non-overlapping pointers
        unsafe {
            ptr::copy(src, dst, rhs.n_keys);
        }
        // SAFETY: Copying values from rhs to self at the appropriate position
        let src = rhs.values.as_mut_ptr();
        // SAFETY: Same bounds as keys array
        let dst = unsafe { self.values.as_mut_ptr().add(self.n_keys) };
        // SAFETY: src and dst are valid, non-overlapping pointers
        unsafe {
            ptr::copy(src, dst, rhs.n_keys);
        }

        // Copy all rhs.n_keys + 1 children from rhs
        for j in 0..=rhs.n_keys {
            self.children[self.n_keys + j] = rhs.children[j];
        }

        self.n_keys += rhs.n_keys;

        assert_eq!(self.n_keys, B::to_usize() * 2);
    }

    fn _pair(&mut self, i: usize) -> (K, V) {
        assert!(i < self.n_keys());
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let key = unsafe { self.keys[i].assume_init_read() };
        // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
        let value = unsafe { self.values[i].assume_init_read() };
        (key, value)
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

    /// # Safety
    ///
    /// Caller must ensure that `i < self.n_keys` and that the node at index `i`
    /// is a leaf entry (no child at `i + 1`).
    #[inline]
    unsafe fn remove_leaf(&mut self, i: usize) -> (K, V) {
        let entry = self._pair(i);

        // SAFETY: Copying keys from i+1 to i, shifting left after removal
        // SAFETY: i + 1 <= n_keys, so offset is within bounds
        let src = unsafe { self.keys.as_mut_ptr().add(i + 1) };
        // SAFETY: i < n_keys, so offset is within bounds
        let dst = unsafe { self.keys.as_mut_ptr().add(i) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }
        // SAFETY: Copying values from i+1 to i, shifting left after removal
        // SAFETY: i + 1 <= n_keys, so offset is within bounds
        let src = unsafe { self.values.as_mut_ptr().add(i + 1) };
        // SAFETY: i < n_keys, so offset is within bounds
        let dst = unsafe { self.values.as_mut_ptr().add(i) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }

        // SAFETY: Copying children from i+2 to i+1, shifting left after removal
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

    #[inline]
    pub fn check_underflow<A: Allocator>(&mut self, alloc: &A, mut i: usize) -> bool {
        assert!(self.children[i].is_some());

        let mut child = self.children[i].as_mut_node_ref();
        assert!(child.n_keys() >= B::to_usize() - 1);

        if child.n_keys() != B::to_usize() - 1 {
            return false;
        }

        // let other = if i > 0 { self.children[i-1].as_mut().unwrap() } else { self.children[1].as_mut().unwrap() };

        if i != 0 {
            let mut lhs = self.children[i - 1].as_mut_node_ref();
            if lhs.n_keys() > B::to_usize() {
                // Borrow an entry from the lhs
                let (entry, lhs_child) = lhs.take_last_child();
                let entry = self._replace_entry(i - 1, entry);
                child.insert_first_entry(entry, lhs_child);

                return false;
            }
        }

        if i != self.n_keys {
            let mut rhs = self.children[i + 1].as_mut_node_ref();
            if rhs.n_keys() > B::to_usize() {
                // Borrow an entry from the rhs
                let (entry, rhs_child) = rhs.take_first_child();
                let entry = self._replace_entry(i, entry);
                child.insert_last_entry(entry, rhs_child);

                return false;
            }
        }

        // Merge
        if i == 0 {
            i = 1;
        }

        let pair = self._pair(i - 1);
        let child = self.take_child_at_in(alloc, i);
        self.child_at_mut(i - 1).unwrap().merge(pair, child);

        // SAFETY: Copying keys from i to i-1, shifting left after merge
        // SAFETY: i <= n_keys, so offset is within bounds
        let src = unsafe { self.keys.as_mut_ptr().add(i) };
        // SAFETY: i >= 1, so i - 1 >= 0 and within bounds
        let dst = unsafe { self.keys.as_mut_ptr().add(i - 1) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }

        // SAFETY: Copying values from i to i-1, shifting left after merge
        // SAFETY: i <= n_keys, so offset is within bounds
        let src = unsafe { self.values.as_mut_ptr().add(i) };
        // SAFETY: i >= 1, so i - 1 >= 0 and within bounds
        let dst = unsafe { self.values.as_mut_ptr().add(i - 1) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }

        // SAFETY: Copying children from i+1 to i, shifting left after merge
        // SAFETY: i + 1 <= n_keys + 1 <= capacity, so offset is within bounds
        let src = unsafe { self.children.as_mut_ptr().add(i + 1) };
        // SAFETY: i <= n_keys < capacity, so offset is within bounds
        let dst = unsafe { self.children.as_mut_ptr().add(i) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys - i);
        }

        self.n_keys -= 1;

        true
    }

    pub fn take_last_child(&mut self) -> ((K, V), ChildPtr) {
        let entry = self.take_key_value_at(self.n_keys - 1);
        let child = self.children[self.n_keys].take();
        self.n_keys -= 1;

        (entry, child)
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn remove_from_here_in<A: Allocator>(&mut self, alloc: &A, i: usize) -> (K, V) {
        match self.children[i + 1].as_option_mut_node_ref() {
            // SAFETY: Caller guarantees i is valid and this is a leaf entry
            None => unsafe { self.remove_leaf(i) },
            Some(mut child) => {
                // SAFETY: Index i is valid (< n_keys) so the key and value are initialized
                let key = unsafe { self.keys[i].assume_init_read() };
                // SAFETY: Index i is valid (< n_keys) so values[i] is initialized. Takes ownership.
                let value = unsafe { self.values[i].assume_init_read() };
                let entry = (key, value);

                // SAFETY: Caller guarantees `alloc` is the same allocator used for this tree
                let (k, v) = unsafe { child.remove_first_child(alloc) };
                self.keys[i].write(k);
                self.values[i].write(v);

                self.check_underflow(alloc, i + 1);

                entry
            }
        }
    }
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> DropIn
    for InteriorNode<K, V, B>
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
        // SAFETY: alloc matches the allocator used to create all children
        unsafe {
            for i in 0..=self.n_keys {
                // if let Some(mut ptr) = self.children[i].as_option_mut_node_ref() {
                //     ptr.as_mut().drop_in(alloc);
                //     alloc.deallocate(ptr.cast(), Layout::new::<InteriorNode<K, V, B>>());
                // }
                self.children[i].drop_and_deallocate_in::<A, K, V, B>(alloc);
            }
        }
    }
}

#[cfg(feature = "std")]
impl<K: core::cmp::PartialOrd + Debug, V: Debug, B: ArrayLength> InteriorNode<K, V, B>
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
            let child = self.children[i].as_option_node_ref::<K, V, B>();
            // let child = self.children[i].to_usize();
            if let Some(child) = child {
                // let that = unsafe { child.as_ref() };
                match child {
                    NodeRef::Interior(that) => {
                        data.write_all(
                            format!("\"p{:?}\" -> \"p{:?}\";\n", this, core::ptr::from_ref(that))
                                .as_bytes(),
                        )?;

                        that.to_dot(data)?;
                    }
                    NodeRef::Leaf(that) => {
                        data.write_all(
                            format!("\"p{:?}\" -> \"p{:?}\";\n", this, core::ptr::from_ref(that))
                                .as_bytes(),
                        )?;

                        that.to_dot(data)?;
                    }
                }
            }
        }

        Ok(())
    }
}
