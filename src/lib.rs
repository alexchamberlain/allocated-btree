//! B-Tree implementations using the _allocated_ pattern for explicit allocator control.
//!
//! This crate provides two B-Tree map implementations designed to demonstrate
//! and compare memory usage patterns:
//!
//! - [`NaiveBTreeMap`] - A traditional B-Tree with uniform node structure
//! - [`CompressedBTreeMap`] - An optimized B-Tree using ~30% less memory
//!
//! # Quick Start
//!
//! ```
//! use allocated_btree::CompressedBTreeMap;
//!
//! let mut map = CompressedBTreeMap::new();
//! map.insert(1, "one")?;
//! map.insert(2, "two")?;
//! map.insert(3, "three")?;
//!
//! assert_eq!(map.get(&2), Some(&"two"));
//! assert_eq!(map.len(), 3);
//! # Ok::<(), allocated::AllocErrorWithLayout>(())
//! ```
//!
//! # Which Implementation to Use?
//!
//! **Use [`CompressedBTreeMap`]** (recommended) for:
//! - Production use where memory efficiency matters
//! - Large datasets where the ~30% memory savings are significant
//! - General-purpose ordered map needs
//!
//! **Use [`NaiveBTreeMap`]** for:
//! - Learning about B-Tree internals (simpler implementation)
//! - Comparing memory usage patterns
//! - Debugging and testing
//!
//! # The Allocated Pattern
//!
//! This crate follows the _allocated_ pattern, providing two types per implementation:
//!
//! ## Wrapper Types (Recommended)
//!
//! - [`NaiveBTreeMap<K, V, B, A>`] - Owns allocator, safe API
//! - [`CompressedBTreeMap<K, V, B, A>`] - Owns allocator, safe API
//!
//! These are ergonomic wrappers that own their allocator and provide safe methods:
//!
//! ```
//! use allocated_btree::NaiveBTreeMap;
//!
//! let mut map = NaiveBTreeMap::new();
//! map.insert(42, "answer")?;  // No unsafe blocks needed!
//! # Ok::<(), allocated::AllocErrorWithLayout>(())
//! ```
//!
//! ## Allocated Types (Advanced)
//!
//! - [`AllocatedNaiveBTreeMap<K, V, B>`] - Low-level, requires manual allocator passing
//! - [`AllocatedCompressedBTreeMap<K, V, B>`] - Low-level, requires manual allocator passing
//!
//! These are for building composite data structures or when you need fine control:
//!
//! ```
//! use allocated_btree::AllocatedNaiveBTreeMap;
//! use allocated::CountingAllocator;
//!
//! let alloc = CountingAllocator::default();
//! let mut map = AllocatedNaiveBTreeMap::<u32, String>::new_in(&alloc)?;
//!
//! unsafe {
//!     map.insert_in(&alloc, 1, "one".to_string())?;
//! }
//!
//! // Track memory usage
//! println!("Allocations: {}", alloc.n_allocations());
//! # Ok::<(), allocated::AllocErrorWithLayout>(())
//! ```
//!
//! # Memory Comparison
//!
//! The compressed implementation achieves ~30% memory savings by using specialized
//! node types:
//!
//! - **Leaf nodes**: Store only keys and values (no child pointers)
//! - **Interior nodes**: Store keys, values, and child pointers
//!
//! The naive implementation uses a single node type with child pointers always
//! allocated, even for leaf nodes.
//!
//! See `examples/memory-comparison.rs` for a detailed comparison across different
//! dataset sizes.

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(any(feature = "std", test))]
extern crate std;

extern crate alloc;

/// Naive B-Tree implementation using a uniform node structure.
///
/// This module provides [`btree::AllocatedBTreeMap`] and its wrapper
/// [`btree::NaiveBTreeMap`]. All nodes in this implementation use the same
/// structure regardless of whether they are leaf or interior nodes.
pub mod btree;
mod common;
/// Compressed B-Tree implementation using specialized node types.
///
/// This module provides [`compressed::AllocatedBTreeMap`] and its wrapper
/// [`compressed::CompressedBTreeMap`]. This implementation uses ~30% less
/// memory than the naive variant by using different structures for leaf and interior nodes.
pub mod compressed;

// Re-export allocated types for advanced use cases
pub use btree::AllocatedBTreeMap as AllocatedNaiveBTreeMap;
pub use compressed::AllocatedBTreeMap as AllocatedCompressedBTreeMap;

// Re-export wrapper types (recommended for most use cases)
pub use btree::NaiveBTreeMap;
pub use compressed::CompressedBTreeMap;
