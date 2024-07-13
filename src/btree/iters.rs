use core::ops::Add;
use core::ops::Mul;

use allocator_api2::alloc::Allocator;
use generic_array::ArrayLength;
use typenum::{Prod, Sum, U1, U2};

use super::node::{IntoIter as NodeIntoIter, Iter as NodeIter, Node};

/// An iterator over the key-value pairs of a `NaiveBTreeMap`, in sorted order by key.
///
/// This struct is created by the [`iter`](super::AllocatedBTreeMap::iter) method on
/// [`AllocatedBTreeMap`](super::AllocatedBTreeMap). See its documentation for more.
pub struct Iter<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIter<'a, K, V, B, &'a Node<K, V, B>>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Iterator
    for Iter<'a, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// An iterator over the keys of a `NaiveBTreeMap`, in sorted order.
///
/// This struct is created by the [`keys`](super::AllocatedBTreeMap::keys) method on
/// [`AllocatedBTreeMap`](super::AllocatedBTreeMap). See its documentation for more.
pub struct Keys<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIter<'a, K, V, B, &'a Node<K, V, B>>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Iterator
    for Keys<'a, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over the values of a `NaiveBTreeMap`, in order by key.
///
/// This struct is created by the [`values`](super::AllocatedBTreeMap::values) method on
/// [`AllocatedBTreeMap`](super::AllocatedBTreeMap). See its documentation for more.
pub struct Values<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIter<'a, K, V, B, &'a Node<K, V, B>>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Iterator
    for Values<'a, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

/// A mutable iterator over the values of a `NaiveBTreeMap`, in order by key.
///
/// This struct is created by the [`values_mut`](super::AllocatedBTreeMap::values_mut) method on
/// [`AllocatedBTreeMap`](super::AllocatedBTreeMap). See its documentation for more.
pub struct ValuesMut<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIter<'a, K, V, B, &'a mut Node<K, V, B>>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength> Iterator
    for ValuesMut<'a, K, V, B>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

/// An owning iterator over the key-value pairs of a `NaiveBTreeMap`, in sorted order by key.
///
/// This struct is created by the [`into_iter`](std::iter::IntoIterator::into_iter) method on
/// [`NaiveBTreeMap`](super::wrapper::NaiveBTreeMap) (provided by the [`IntoIterator`] trait).
pub struct IntoIter<
    'a,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
    A: 'a + Allocator,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIntoIter<'a, K, V, B, A>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: 'a + Allocator> Iterator
    for IntoIter<'a, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// An owning iterator over the keys of a `NaiveBTreeMap`, in sorted order.
///
/// This struct is created internally when converting the map into an iterator over keys.
pub struct IntoKeys<
    'a,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
    A: 'a + Allocator,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIntoIter<'a, K, V, B, A>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: 'a + Allocator> Iterator
    for IntoKeys<'a, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An owning iterator over the values of a `NaiveBTreeMap`, in order by key.
///
/// This struct is created internally when converting the map into an iterator over values.
pub struct IntoValues<
    'a,
    K: core::cmp::PartialOrd + core::fmt::Debug,
    V,
    B: ArrayLength,
    A: 'a + Allocator,
> where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    pub(super) inner: NodeIntoIter<'a, K, V, B, A>,
}

impl<'a, K: core::cmp::PartialOrd + core::fmt::Debug, V, B: ArrayLength, A: 'a + Allocator> Iterator
    for IntoValues<'a, K, V, B, A>
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}
