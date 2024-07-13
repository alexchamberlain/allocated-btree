use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Debug;
use core::mem::MaybeUninit;
use core::ops::Add;
use core::ops::Mul;
use core::ptr;
use core::ptr::NonNull;
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
use generic_array::ArrayLength;
use generic_array::GenericArray;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use super::child_ptr::ChildPtr;
use super::interior_node::InteriorNode;
use super::node_ref::MutNodeRef;
use super::InsertOption;
use super::OccupiedNodeEntry;
use super::VacantNodeEntry;
use super::{Node, NodeEntry};

type Keys<K, B> = GenericArray<MaybeUninit<K>, Prod<U2, B>>;
type Values<V, B> = GenericArray<MaybeUninit<V>, Prod<U2, B>>;
type Children<B> = GenericArray<ChildPtr, Sum<U1, Prod<U2, B>>>;

#[derive(Debug)]
pub struct LeafNode<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    keys: Keys<K, B>,
    values: Values<V, B>,
    n_keys: usize,
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> LeafNode<K, V, B>
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
                LeafNode {
                    keys: GenericArray::uninit(),
                    values: GenericArray::uninit(),
                    n_keys: 0,
                },
                alloc,
            )
        }
    }

    pub fn right<'a, A: Allocator>(
        alloc: &'a A,
        keys: &mut [MaybeUninit<K>],
        values: &mut [MaybeUninit<V>],
        // first_child: ChildPtr,
    ) -> DropGuard<Node<K, V, B>, &'a A> {
        assert_eq!(keys.len(), values.len());
        // assert_eq!(keys.len(), children.len());
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

        // SAFETY: The allocator is valid and matches the one used for allocation
        unsafe {
            DropGuard::new(
                Node::Leaf(Self {
                    keys: new_keys,
                    values: new_values,
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
        keys: &mut [MaybeUninit<K>],
        values: &mut [MaybeUninit<V>],
    ) -> DropGuardResult<Node<K, V, B>, &'a A> {
        assert_eq!(keys.len(), B::to_usize() - 1);
        // SAFETY: We're only reading from initialized keys in the slice
        let i = keys
            .iter()
            .position(|k| unsafe { *k.assume_init_ref() >= key });
        match i {
            None => {
                let mut new_keys = GenericArray::uninit();
                // SAFETY: Copying MaybeUninit data from keys slice to new_keys array
                unsafe {
                    ptr::copy(keys.as_mut_ptr(), new_keys.as_mut_ptr(), keys.len());
                }
                // SAFETY: Writing new key to the end of the array
                unsafe {
                    ptr::write(new_keys[keys.len()].as_mut_ptr(), key);
                }
                let mut new_values = GenericArray::uninit();
                // SAFETY: Copying MaybeUninit data from values slice to new_values array
                unsafe {
                    ptr::copy(values.as_mut_ptr(), new_values.as_mut_ptr(), values.len());
                }
                // SAFETY: Writing new value to the end of the array
                unsafe {
                    ptr::write(new_values[values.len()].as_mut_ptr(), value);
                }

                // SAFETY: The allocator is valid and matches the one used for allocation
                Ok(unsafe {
                    DropGuard::new(
                        Node::Leaf(LeafNode {
                            keys: new_keys,
                            values: new_values,
                            n_keys: B::to_usize(),
                        }),
                        alloc,
                    )
                })
            }
            Some(i) => {
                // SAFETY: Index i is valid so the key is initialized
                assert!(&key < unsafe { keys[i].assume_init_ref() });
                // todo!()
                let mut new_keys = GenericArray::uninit();
                // SAFETY: Copying first i keys
                unsafe {
                    ptr::copy(keys.as_mut_ptr(), new_keys.as_mut_ptr(), i);
                }
                // SAFETY: Writing new key at position i
                unsafe {
                    ptr::write(new_keys[i].as_mut_ptr(), key);
                }
                // SAFETY: Copying remaining keys after insertion point
                unsafe {
                    let src = keys.as_mut_ptr().wrapping_add(i);
                    let dst = new_keys.as_mut_ptr().wrapping_add(i + 1);
                    ptr::copy(src, dst, keys.len() - i);
                }

                let mut new_values = GenericArray::uninit();
                // SAFETY: Copying first i values
                unsafe {
                    ptr::copy(values.as_mut_ptr(), new_values.as_mut_ptr(), i);
                }
                // SAFETY: Writing new value at position i
                unsafe {
                    ptr::write(new_values[i].as_mut_ptr(), value);
                }
                // SAFETY: Copying remaining values after insertion point
                unsafe {
                    let src = values.as_mut_ptr().wrapping_add(i);
                    let dst = new_values.as_mut_ptr().wrapping_add(i + 1);
                    ptr::copy(src, dst, values.len() - i);
                }

                // SAFETY: The allocator is valid and matches the one used for allocation
                Ok(unsafe {
                    DropGuard::new(
                        Node::Leaf(LeafNode {
                            keys: new_keys,
                            values: new_values,
                            n_keys: B::to_usize(),
                        }),
                        alloc,
                    )
                })
            }
        }
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

    pub fn child_at(&self, i: usize) -> Option<&NonNull<InteriorNode<K, V, B>>> {
        assert!(i <= self.n_keys);
        None
    }

    /// # Safety
    ///
    /// `parents` must be the ancestors of this node.
    pub unsafe fn entry_in(
        &mut self,
        key: K,
        mut parents: Vec<(ChildPtr, usize)>,
    ) -> NodeEntry<'_, K, K, V, B, MutNodeRef<'_, K, V, B>> {
        let (i, match_) = self.find(&key);

        if match_ {
            return NodeEntry::Occupied(OccupiedNodeEntry::new(parents, MutNodeRef::Leaf(self), i));
        }

        parents.push((ChildPtr::from_leaf_node(self.into()), i));

        let parents = parents.into_iter().map(|(n, _)| n).collect();
        NodeEntry::Vacant(VacantNodeEntry::<K, K, V, B, MutNodeRef<K, V, B>>::new(
            key, parents, i,
        ))
    }

    // pub fn ref_entry(
    //     &self,
    //     key: K,
    //     mut parents: Vec<(*const Self, usize)>,
    // ) -> NodeEntry<'_, K, K, V, B, &InteriorNode<K, V, B>> {
    //     let (i, match_) = self.find(&key);

    //     if match_ {
    //         return NodeEntry::Occupied(OccupiedNodeEntry::new(parents, self, i));
    //     }

    //     parents.push((self, i));
    //     let child = self.children[i];

    //     match child.as_option_node_ref() {
    //         None => {
    //             let parents = parents.into_iter().map(|(n, _)| n).collect();
    //             NodeEntry::Vacant(VacantNodeEntry::new(key, parents, i))
    //         }
    //         Some(mut child) => child.ref_entry(key, parents),
    //     }
    // }

    pub fn find<Q>(&self, search_key: &Q) -> (usize, bool)
    where
        K: Borrow<Q> + PartialOrd,
        Q: PartialOrd + ?Sized + core::fmt::Debug,
    {
        // println!("find {:?}", search_key);
        for i in 0..self.n_keys {
            // println!("find {} {:?}", i, self.key_at(i));
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
    ) -> AllocResult<InsertOption<'a, 's, K, V, B, A>> {
        let b = B::to_usize();
        if self.n_keys == b * 2 {
            // assert!(rhn.is_none()); // TODO
            // unsafe { std::intrinsics::breakpoint(); }
            // SAFETY: n_keys == b * 2, so keys[b] is initialized
            let old_median = unsafe { self.keys[b].assume_init_ref() };
            // assert_ne!(key, *old_median);
            if key < *old_median {
                if i == b {
                    let new_rhn =
                        LeafNode::right(alloc, &mut self.keys[b..], &mut self.values[b..]);

                    self.n_keys = b;
                    assert_eq!(new_rhn.n_keys(), b);

                    Ok(InsertOption::Split((key, value, new_rhn)))
                } else {
                    let new_rhn =
                        LeafNode::right(alloc, &mut self.keys[b..], &mut self.values[b..]);
                    // SAFETY: n_keys was b * 2, so keys[b - 1] is initialized
                    let median_key = unsafe { self.keys[b - 1].assume_init_read() };
                    // SAFETY: n_keys was b * 2, so values[b - 1] is initialized
                    let median_value = unsafe { self.values[b - 1].assume_init_read() };
                    self.n_keys = b - 1;

                    // SAFETY: Caller guarantees `alloc` is the allocator used for this tree
                    let r = unsafe { self.insert_in_here(alloc, key, value, i)? };
                    assert!(r.is_new_key());
                    assert_eq!(self.n_keys, b);
                    assert_eq!(new_rhn.n_keys(), b);

                    Ok(InsertOption::Split((median_key, median_value, new_rhn)))
                }
            } else {
                let rhn = LeafNode::right_1(
                    alloc,
                    key,
                    value,
                    &mut self.keys[b + 1..],
                    &mut self.values[b + 1..],
                )?;
                self.n_keys = b;
                Ok(InsertOption::Split((
                    // SAFETY: n_keys was b * 2, so keys[b] is initialized
                    unsafe { self.keys[b].assume_init_read() },
                    // SAFETY: n_keys was b * 2, so values[b] is initialized
                    unsafe { self.values[b].assume_init_read() },
                    rhn,
                )))
            }
        } else {
            assert!(self.n_keys >= i);
            // SAFETY: Copying keys from i to i+1, shifting right to make room for insertion
            // SAFETY: i <= n_keys, so offset is within bounds
            let src = unsafe { self.keys.as_mut_ptr().add(i) };
            // SAFETY: i + 1 <= n_keys + 1, so offset is within bounds
            let dst = unsafe { self.keys.as_mut_ptr().add(i + 1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys - i);
            }
            self.keys[i].write(key);

            // SAFETY: Copying values from i to i+1, shifting right to make room for insertion
            // SAFETY: i <= n_keys, so offset is within bounds
            let src = unsafe { self.values.as_mut_ptr().add(i) };
            // SAFETY: i + 1 <= n_keys + 1, so offset is within bounds
            let dst = unsafe { self.values.as_mut_ptr().add(i + 1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys - i);
            }
            self.values[i].write(value);
            self.n_keys += 1;

            // SAFETY: We just wrote value at index i, so values[i] is initialized
            Ok(InsertOption::NewKey(unsafe {
                self.values[i].assume_init_mut()
            }))
        }
    }

    pub fn insert_first_entry(&mut self, entry: (K, V), child: ChildPtr) {
        // unsafe { std::intrinsics::breakpoint(); }

        assert!(child.is_null());

        if self.n_keys > 0 {
            // SAFETY: n_keys > 0, so keys[0] is initialized
            assert!(&entry.0 < unsafe { self.keys[0].assume_init_ref() });

            // SAFETY: Copying keys from index 0 to 1, shifting right to make room
            // SAFETY: Offset 0 is always valid
            let src = unsafe { self.keys.as_mut_ptr().add(0) };
            // SAFETY: Offset 1 is within bounds
            let dst = unsafe { self.keys.as_mut_ptr().add(1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys);
            }
            // SAFETY: Copying values from index 0 to 1, shifting right to make room
            // SAFETY: Offset 0 is always valid
            let src = unsafe { self.values.as_mut_ptr().add(0) };
            // SAFETY: Offset 1 is within bounds
            let dst = unsafe { self.values.as_mut_ptr().add(1) };
            // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
            unsafe {
                ptr::copy(src, dst, self.n_keys);
            }
        }

        self.keys[0].write(entry.0);
        self.values[0].write(entry.1);

        self.n_keys += 1;
    }

    pub fn insert_last_entry(&mut self, entry: (K, V), child: ChildPtr) {
        assert!(child.is_null());
        self._insert_last_entry(entry);
    }

    fn _insert_last_entry(&mut self, entry: (K, V) /*, child: ChildPtr */) {
        // unsafe { std::intrinsics::breakpoint(); }

        if self.n_keys > 0 {
            let i = self.n_keys - 1;
            // SAFETY: i = n_keys - 1 < n_keys, so keys[i] is initialized
            assert!(unsafe { self.keys[i].assume_init_ref() } < &entry.0);
        }

        self.keys[self.n_keys].write(entry.0);
        self.values[self.n_keys].write(entry.1);
        // self.children[self.n_keys + 1] = child;

        self.n_keys += 1;
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn remove_from_here_in<A: Allocator>(&mut self, _alloc: &A, i: usize) -> (K, V) {
        // SAFETY: Caller ensures i is valid and alloc matches
        unsafe { self.remove_leaf(i) }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to allocate children in this node.
    pub unsafe fn remove_first_child<A: Allocator>(&mut self, _alloc: &A) -> (K, V) {
        // SAFETY: Removing from index 0, caller ensures alloc matches
        unsafe { self.remove_leaf(0) }
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
    /// Caller must ensure that `i < self.n_keys`.
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

        self.n_keys -= 1;
        entry
    }

    pub fn merge(&mut self, pair: (K, V), mut rhs: LeafNode<K, V, B>) {
        assert!(self.n_keys + rhs.n_keys + 1 == B::to_usize() * 2);

        self._write_pair(self.n_keys, pair);
        self.n_keys += 1;

        // SAFETY: Copying keys from rhs to self at the appropriate position
        // SAFETY: Offset 0 is always valid
        let src = rhs.keys.as_mut_ptr();
        // SAFETY: n_keys is within bounds after incrementing
        let dst = unsafe { self.keys.as_mut_ptr().add(self.n_keys) };
        // SAFETY: src and dst are valid pointers in separate arrays, no overlap
        unsafe {
            ptr::copy(src, dst, rhs.n_keys);
        }
        // SAFETY: Copying values from rhs to self at the appropriate position
        // SAFETY: Offset 0 is always valid
        let src = rhs.values.as_mut_ptr();
        // SAFETY: n_keys is within bounds after incrementing
        let dst = unsafe { self.values.as_mut_ptr().add(self.n_keys) };
        // SAFETY: src and dst are valid pointers in separate arrays, no overlap
        unsafe {
            ptr::copy(src, dst, rhs.n_keys);
        }

        self.n_keys += rhs.n_keys;

        assert_eq!(self.n_keys, B::to_usize() * 2);
    }

    pub fn take_last_child(&mut self) -> ((K, V), ChildPtr) {
        let entry = self.take_key_value_at(self.n_keys - 1);
        self.n_keys -= 1;

        (entry, ChildPtr::null())
    }

    pub fn take_first_child(&mut self) -> ((K, V), ChildPtr) {
        let entry = self.take_key_value_at(0);
        self.n_keys -= 1;

        // SAFETY: Copying keys from index 1 to 0, shifting left after removal
        // SAFETY: Offset 1 is within bounds
        let src = unsafe { self.keys.as_mut_ptr().add(1) };
        // SAFETY: Offset 0 is always valid
        let dst = unsafe { self.keys.as_mut_ptr().add(0) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys);
        }

        // SAFETY: Copying values from index 1 to 0, shifting left after removal
        // SAFETY: Offset 1 is within bounds
        let src = unsafe { self.values.as_mut_ptr().add(1) };
        // SAFETY: Offset 0 is always valid
        let dst = unsafe { self.values.as_mut_ptr().add(0) };
        // SAFETY: src and dst are valid pointers, ptr::copy handles overlaps
        unsafe {
            ptr::copy(src, dst, self.n_keys);
        }

        (entry, ChildPtr::null())
    }
}

impl<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> DropIn for LeafNode<K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    /// # Safety
    ///
    /// `alloc` must be the allocator used to allocate this object.
    unsafe fn drop_in<A: Allocator>(&mut self, _alloc: &A) {
        // TODO!
        for _i in 0..=self.n_keys {
            // if let Some(mut ptr) = self.children[i] {
            //     ptr.as_mut().drop_in(alloc);
            //     alloc.deallocate(ptr.cast(), Layout::new::<InteriorNode<K, V, B>>());
            // }
        }
    }
}
#[cfg(feature = "std")]
impl<K: core::cmp::PartialOrd + Debug, V: Debug, B: ArrayLength> LeafNode<K, V, B>
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

        Ok(())
    }
}
