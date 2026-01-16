use crate::common::TakeInsertExt;
use core::alloc::Layout;
use core::ops::Add;
use core::ops::Mul;
use core::ptr::NonNull;
use generic_array::sequence::GenericSequence;
use generic_array::GenericArray;

use allocator_api2::alloc::Allocator;
use generic_array::ArrayLength;
use typenum::Prod;
use typenum::Sum;
use typenum::U1;
use typenum::U2;

use allocated::{AllocResult, AllocatorExt, DropIn};

use super::node_ref::{MutNodeRef, NodeRef};
use super::{InteriorNode, LeafNode, Node};

const INTERIOR_FLAG: usize = 1;
const INTERIOR_MASK: usize = !1;

#[derive(Debug, Copy, Clone)]
pub struct ChildPtr(usize);

impl ChildPtr {
    pub fn null() -> Self {
        Self(0)
    }

    pub fn take(&mut self) -> Self {
        let ret = *self;
        self.0 = 0;
        ret
    }

    pub fn is_null(&self) -> bool {
        self.0 == 0
    }

    pub fn is_some(&self) -> bool {
        self.0 > 0
    }

    pub fn from_leaf_node<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        node: NonNull<LeafNode<K, V, B>>,
    ) -> Self
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        Self(node.as_ptr() as usize)
    }

    pub fn from_interior_node<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        node: NonNull<InteriorNode<K, V, B>>,
    ) -> Self
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        Self((node.as_ptr() as usize) | 1)
    }

    pub fn from_node_in<
        A: Allocator,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        alloc: &A,
        child: Node<K, V, B>,
    ) -> AllocResult<ChildPtr>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        match child {
            Node::Interior(child) => {
                let lh_heap = alloc.allocate_from(child)?;
                Ok(Self::from_interior_node(lh_heap.into_inner()))
            }
            Node::Leaf(child) => {
                let lh_heap = alloc.allocate_from(child)?;
                Ok(Self::from_leaf_node(lh_heap.into_inner()))
            }
        }
    }

    pub fn replace(&mut self, other: Self) {
        assert_eq!(self.0, 0);
        self.0 = other.0;
    }

    pub fn as_node_ref<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        &self,
    ) -> NodeRef<'_, K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            // let ptr: NonNull<InteriorNode<K, V, B>> = NonNull::new(self.0 as *const _).unwrap();
            let ptr = (self.0 & INTERIOR_MASK) as *const InteriorNode<K, V, B>;
            // SAFETY: The ChildPtr was created from a valid InteriorNode pointer and has not been deallocated
            NodeRef::Interior(unsafe { &*ptr })
        } else {
            // let ptr: NonNull<LeafNode<K, V, B>> = NonNull::new(self.0 as *const _).unwrap();
            let ptr = self.0 as *const LeafNode<K, V, B>;
            // SAFETY: The ChildPtr was created from a valid LeafNode pointer and has not been deallocated
            NodeRef::Leaf(unsafe { &*ptr })
        }
    }

    /// Converts this `ChildPtr` to a `NodeRef` with an explicitly specified lifetime.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// 1. The `ChildPtr` points to a valid node that has not been deallocated
    /// 2. The node lives at least as long as the specified lifetime `'a`
    /// 3. No mutable references to the same node exist during the lifetime `'a`
    pub unsafe fn as_node_ref_with_lifetime<
        'a,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        &self,
    ) -> NodeRef<'a, K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            let ptr = (self.0 & INTERIOR_MASK) as *const InteriorNode<K, V, B>;
            // SAFETY: Caller ensures the pointer is valid for lifetime 'a
            NodeRef::Interior(unsafe { &*ptr })
        } else {
            // Leaf Node
            let ptr = self.0 as *const LeafNode<K, V, B>;
            // SAFETY: Caller ensures the pointer is valid for lifetime 'a
            NodeRef::Leaf(unsafe { &*ptr })
        }
    }

    /// Gets a reference to a key at the specified index in the node this `ChildPtr` points to.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// 1. The `ChildPtr` points to a valid node that has not been deallocated
    /// 2. The node lives at least as long as the specified lifetime `'a`
    /// 3. The index `i` is valid for the node (i < n_keys)
    /// 4. No mutable references to the same node exist during the lifetime `'a`
    pub unsafe fn get_key_at<
        'a,
        K: core::cmp::PartialOrd + core::fmt::Debug + 'a,
        V: 'a,
        B: ArrayLength,
    >(
        &self,
        i: usize,
    ) -> &'a K
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            let ptr = (self.0 & INTERIOR_MASK) as *const InteriorNode<K, V, B>;
            // SAFETY: Caller ensures pointer is valid for lifetime 'a and index is valid
            unsafe { (&*ptr).key_at(i) }
        } else {
            // Leaf Node
            let ptr = self.0 as *const LeafNode<K, V, B>;
            // SAFETY: Caller ensures pointer is valid for lifetime 'a and index is valid
            unsafe { (&*ptr).key_at(i) }
        }
    }

    /// Gets a reference to a value at the specified index in the node this `ChildPtr` points to.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// 1. The `ChildPtr` points to a valid node that has not been deallocated
    /// 2. The node lives at least as long as the specified lifetime `'a`
    /// 3. The index `i` is valid for the node (i < n_keys)
    /// 4. No mutable references to the same node exist during the lifetime `'a`
    pub unsafe fn get_value_at<
        'a,
        K: core::cmp::PartialOrd + core::fmt::Debug + 'a,
        V: 'a,
        B: ArrayLength,
    >(
        &self,
        i: usize,
    ) -> &'a V
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            let ptr = (self.0 & INTERIOR_MASK) as *const InteriorNode<K, V, B>;
            // SAFETY: Caller ensures pointer is valid for lifetime 'a and index is valid
            unsafe { (&*ptr).value_at(i) }
        } else {
            // Leaf Node
            let ptr = self.0 as *const LeafNode<K, V, B>;
            // SAFETY: Caller ensures pointer is valid for lifetime 'a and index is valid
            unsafe { (&*ptr).value_at(i) }
        }
    }

    pub fn from_node_ref<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        node_ref: NodeRef<'_, K, V, B>,
    ) -> Self
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        match node_ref {
            NodeRef::Interior(node) => Self::from_interior_node(node.into()),
            NodeRef::Leaf(node) => Self::from_leaf_node(node.into()),
        }
    }

    pub fn from_mut_node_ref<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        node_ref: &mut MutNodeRef<'_, K, V, B>,
    ) -> Self
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        match node_ref {
            MutNodeRef::Interior(node) => {
                // SAFETY: We have exclusive access to the interior node through the mutable reference
                let ptr = unsafe { NonNull::new_unchecked(&mut **node) };
                Self::from_interior_node(ptr)
            }
            MutNodeRef::Leaf(node) => {
                // SAFETY: We have exclusive access to the leaf node through the mutable reference
                let ptr = unsafe { NonNull::new_unchecked(&mut **node) };
                Self::from_leaf_node(ptr)
            }
        }
    }

    /// # Safety
    ///
    /// Caller is specifying the lifetime `'s`
    pub unsafe fn unsafe_as_node_ref<
        's,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        self,
    ) -> NodeRef<'s, K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            let ptr = (self.0 & INTERIOR_MASK) as *const InteriorNode<K, V, B>;
            // SAFETY: Caller guarantees the lifetime 's is valid for this pointer
            NodeRef::Interior(unsafe { &*ptr })
        } else {
            let ptr = self.0 as *const LeafNode<K, V, B>;
            // SAFETY: Caller guarantees the lifetime 's is valid for this pointer
            NodeRef::Leaf(unsafe { &*ptr })
        }
    }

    pub fn as_option_node_ref<K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        &self,
    ) -> Option<NodeRef<'_, K, V, B>>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if self.0 == 0 {
            return None;
        }

        Some(self.as_node_ref())
    }

    pub fn as_mut_node_ref<'s, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>(
        self,
    ) -> MutNodeRef<'s, K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            let mut ptr: NonNull<InteriorNode<K, V, B>> =
                NonNull::new((self.0 & INTERIOR_MASK) as *mut _).unwrap();
            // SAFETY: The ChildPtr was created from a valid InteriorNode pointer and has not been deallocated
            let node = unsafe { ptr.as_mut() };
            MutNodeRef::Interior(node)
        } else {
            let mut ptr: NonNull<LeafNode<K, V, B>> = NonNull::new(self.0 as *mut _).unwrap();
            // SAFETY: The ChildPtr was created from a valid LeafNode pointer and has not been deallocated
            let node = unsafe { ptr.as_mut() };
            MutNodeRef::Leaf(node)
        }
    }

    /// # Safety
    ///
    /// Caller is specifying the lifetime `'s`
    pub unsafe fn as_mut_interior_node<
        's,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        self,
    ) -> &'s mut InteriorNode<K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        assert_eq!((self.0 & 1), 1);
        let mut ptr: NonNull<InteriorNode<K, V, B>> =
            NonNull::new((self.0 & INTERIOR_MASK) as *mut _).unwrap();
        // SAFETY: Caller guarantees the lifetime 's is valid, and we verified this is an interior node
        unsafe { ptr.as_mut() }
    }

    /// # Safety
    ///
    /// Caller is specifying the lifetime `'s`
    pub unsafe fn unsafe_as_mut_node_ref<
        's,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        self,
    ) -> MutNodeRef<'s, K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if (self.0 & 1) > 0 {
            // Interior Node
            let mut ptr: NonNull<InteriorNode<K, V, B>> =
                NonNull::new((self.0 & INTERIOR_MASK) as *mut _).unwrap();
            // SAFETY: Caller guarantees the lifetime 's is valid for this pointer
            let node = unsafe { ptr.as_mut() };
            MutNodeRef::Interior(node)
        } else {
            let mut ptr: NonNull<LeafNode<K, V, B>> = NonNull::new(self.0 as *mut _).unwrap();
            // SAFETY: Caller guarantees the lifetime 's is valid for this pointer
            let node = unsafe { ptr.as_mut() };
            MutNodeRef::Leaf(node)
        }
    }

    pub fn as_option_mut_node_ref<
        's,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        self,
    ) -> Option<MutNodeRef<'s, K, V, B>>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if self.0 == 0 {
            return None;
        }

        Some(self.as_mut_node_ref())
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to create this pointer.
    pub unsafe fn drop_and_deallocate_in<
        A: Allocator,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        self,
        alloc: &A,
    ) where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        if self.0 == 0 {
            // Null pointer, nothing to do
        } else if (self.0 & 1) > 0 {
            // Interior Node
            let mut ptr: NonNull<InteriorNode<K, V, B>> =
                NonNull::new((self.0 & INTERIOR_MASK) as *mut _).unwrap();
            // SAFETY: The pointer was created from a valid allocation with the same allocator
            let node = unsafe { ptr.as_mut() };
            // SAFETY: Caller guarantees `alloc` is the same allocator used to create this node
            unsafe { node.drop_in(alloc) };
            // SAFETY: The pointer was allocated with this allocator and layout
            unsafe { alloc.deallocate(ptr.cast(), Layout::new::<InteriorNode<K, V, B>>()) };
        } else {
            let mut ptr: NonNull<LeafNode<K, V, B>> = NonNull::new(self.0 as *mut _).unwrap();
            // SAFETY: The pointer was created from a valid allocation with the same allocator
            let node = unsafe { ptr.as_mut() };
            // SAFETY: Caller guarantees `alloc` is the same allocator used to create this node
            unsafe { node.drop_in(alloc) };
            // SAFETY: The pointer was allocated with this allocator and layout
            unsafe { alloc.deallocate(ptr.cast(), Layout::new::<LeafNode<K, V, B>>()) };
        }
    }

    /// # Safety
    ///
    /// `alloc` MUST be the allocator used to create this pointer.
    pub unsafe fn read_and_deallocate_in<
        A: Allocator,
        K: core::cmp::PartialOrd + core::fmt::Debug,
        V,
        B: ArrayLength,
    >(
        self,
        alloc: &A,
    ) -> Node<K, V, B>
    where
        U2: Mul<B>,
        Prod<U2, B>: ArrayLength,
        U1: Add<Prod<U2, B>>,
        Sum<U1, Prod<U2, B>>: ArrayLength,
    {
        assert!(self.0 != 0);

        if (self.0 & 1) > 0 {
            let mut child_ptr: NonNull<InteriorNode<K, V, B>> =
                NonNull::new((self.0 & INTERIOR_MASK) as *mut _).unwrap();
            // SAFETY: The pointer was created from a valid allocation with the same allocator
            let ptr = unsafe { child_ptr.as_mut() };
            // SAFETY: Caller guarantees this pointer is valid and won't be used again
            let interior_node: InteriorNode<_, _, _> = unsafe { core::ptr::read(ptr) };
            // SAFETY: The pointer was allocated with this allocator and layout
            unsafe { alloc.deallocate(child_ptr.cast(), Layout::new::<InteriorNode<K, V, B>>()) };
            Node::Interior(interior_node)
        } else {
            let mut child_ptr: NonNull<LeafNode<K, V, B>> = NonNull::new(self.0 as *mut _).unwrap();
            // SAFETY: The pointer was created from a valid allocation with the same allocator
            let ptr = unsafe { child_ptr.as_mut() };
            // SAFETY: Caller guarantees this pointer is valid and won't be used again
            let leaf_node: LeafNode<_, _, _> = unsafe { core::ptr::read(ptr) };
            // SAFETY: The pointer was allocated with this allocator and layout
            unsafe { alloc.deallocate(child_ptr.cast(), Layout::new::<LeafNode<K, V, B>>()) };
            Node::Leaf(leaf_node)
        }
    }
}

impl<B: generic_array::ArrayLength> TakeInsertExt<ChildPtr, ChildPtr>
    for GenericArray<ChildPtr, B>
{
    fn pop_at(&mut self, idx: usize, len: usize) -> ChildPtr {
        assert!(len <= B::to_usize());
        let value = self[idx];
        // SAFETY: We're copying within the same array, source and destination don't overlap
        // because we copy from idx+1 to idx (moving elements left by one)
        // SAFETY: idx + 1 <= len <= capacity, so this offset is within bounds
        let src = unsafe { self.as_mut_ptr().add(idx + 1) };
        // SAFETY: idx < len (implied by removing at idx), so idx is within bounds
        let dst = unsafe { self.as_mut_ptr().add(idx) };
        // SAFETY: src and dst are valid pointers, copy moves elements left to fill gap
        unsafe {
            core::ptr::copy(src, dst, len - idx - 1);
        }
        value
    }

    fn take(other: &mut [ChildPtr]) -> Self {
        assert!(other.len() <= B::to_usize());
        GenericArray::generate(|j| {
            if j < other.len() {
                other[j]
            } else {
                ChildPtr::null()
            }
        })
    }

    fn take_and_insert(other: &mut [ChildPtr], idx: usize, len: usize, value: ChildPtr) -> Self {
        assert!(len <= B::to_usize());
        assert!(idx <= len);
        let mut new_children = GenericArray::generate(|j| {
            if j < idx {
                other[j]
            } else if j == idx {
                ChildPtr::null()
            } else if j - 1 < other.len() {
                other[j - 1]
            } else {
                ChildPtr::null()
            }
        });
        new_children[idx] = value;
        new_children
    }
}
