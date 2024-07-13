# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Rust crate implementing B-Tree data structures using the "allocated pattern" - a memory management pattern that provides explicit allocator control. The crate provides two main interfaces:

- `AllocatedNaiveBTreeMap` - A naive B-Tree using a single node shape
- `AllocatedCompressedBTreeMap` - An optimized B-Tree with compressed leaf nodes (uses ~50% less memory)

The primary purpose is to serve as an example of using the `allocated` crate for comparing data structure memory usage.

## Build, Test, and Development Commands

### Building
```bash
cargo build
cargo build --release
```

### Testing
```bash
# Run all tests
cargo test

# Run a single test
cargo test test_name

# Run tests with proptest (property-based testing)
cargo test test_uints
cargo test test_strings

# Run with output visible
cargo test -- --nocapture
```

### Linting
```bash
# Run clippy with the project's custom configuration (clippy.toml)
cargo clippy

# The project enforces:
# - undocumented_unsafe_blocks = warn
# - multiple_unsafe_ops_per_block = warn
# - check-private-items = true
```

### Coverage
The project uses tarpaulin for code coverage. A coverage report exists at `tarpaulin-report.html`.

## Architecture

### Two Parallel B-Tree Implementations

The codebase contains two complete B-Tree implementations that mirror each other:

1. **Naive B-Tree** (`src/btree.rs`): Uses a single `Node` struct for all nodes
2. **Compressed B-Tree** (`src/compressed.rs`): Uses specialized `InteriorNode` and `LeafNode` types

Both implementations share:
- The same public API surface (`AllocatedBTreeMap`)
- Similar internal structure (entries, nodes, iterators)
- Identical test patterns

### Key Architectural Patterns

**Allocated Pattern**: All data structures use the `allocated` crate's pattern:
- `new_in(&allocator)` for construction
- `drop_in(&allocator)` for destruction (unsafe, requires matching allocator)
- `insert_in(&allocator, ...)` for mutations
- Return types wrapped in `DropGuard` to ensure proper cleanup

**Type-Level Configuration**: B-Tree branching factor is controlled via `typenum`:
- Default branching factor: `B = U6` (6-way tree)
- Array sizes computed at compile-time: `2*B` for keys/values, `2*B+1` for children
- Tests use `B = U1` for simpler validation of edge cases

**Memory Safety**: Heavy use of `unsafe`:
- All `unsafe` blocks must have documentation (enforced by clippy)
- Uses `MaybeUninit` for uninitialized arrays
- Manual memory management via raw pointers and `NonNull`
- `#![deny(unsafe_op_in_unsafe_fn)]` enforced at crate level

### Module Organization

**Naive B-Tree** (`src/btree.rs`):
- Single `Node` struct containing keys, values, and child pointers
- All nodes have the same memory layout regardless of whether they're leaf or interior nodes

**Compressed B-Tree** (`src/compressed/`):
- `node/leaf_node.rs` - Leaf nodes (no child pointers)
- `node/interior_node.rs` - Interior nodes (with child pointers)
- `node/node_ref.rs` - Reference wrappers (`NodeRef`, `MutNodeRef`) for polymorphic access
- `node/child_ptr.rs` - Type-safe child pointer abstraction

**Shared Utilities** (`src/common.rs`):
- `InsertExt` - Insert element into array by shifting
- `TakeInsertExt` - Take elements and insert, used during node splits

Both implementations provide:
- `entry` API (Entry/OccupiedEntry/VacantEntry) similar to std::collections
- Iterator types (Iter, IntoIter, Keys, Values, etc.)
- Entry-based insertion and removal

### Important Implementation Details

**Node Splitting**: When a node exceeds `2*B` keys, it splits:
- Median key is promoted to parent
- Left half stays in original node
- Right half moves to new sibling node

**Entry API Safety**: The `entry()` API uses `NonNull<AllocatedBTreeMap>` to track ownership while navigating the tree, allowing safe insertion/removal through the entry without multiple mutable borrows.

**Allocator Coupling**: All mutation methods are `unsafe` because they require the caller to pass the same allocator used during construction. Passing the wrong allocator causes undefined behavior.

**Underflow Handling (Compressed B-Tree)**: When removing entries causes a node to have fewer than `B-1` keys, the compressed implementation handles underflow through:
1. **Borrowing from siblings**: Try to borrow an entry from left or right sibling if they have spare keys
   - Left sibling: Take last entry, insert at beginning of underflowing node
   - Right sibling: Take first entry, insert at end of underflowing node (critical: must use `insert_last_entry`, not `insert_first_entry`)
2. **Merging nodes**: If siblings can't spare entries, merge with a sibling
   - Interior nodes: Must copy all `n_keys + 1` children (one more child than keys)
   - The parent separator key moves down to become part of the merged node
3. **Root reduction**: If root becomes empty after merge, replace root with its only child

## Testing Strategy

The codebase uses multiple testing approaches:

1. **Unit tests**: Explicit test cases for specific sizes (1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15, 20, 31, 63 elements)
2. **Removal-focused tests**: Tests for repeated minimum removal via `first_entry().remove_entry()`
   - These stress underflow handling, sibling borrowing, and node merging
   - Critical for catching bugs in left/right rebalancing logic
   - Both implementations include comprehensive underflow tests:
     - `test_remove_all_*_elements`: Remove all elements from trees of various sizes
     - `test_remove_pattern_causing_left_borrow`: Forces left sibling borrowing
     - `test_remove_pattern_causing_right_borrow`: Forces right sibling borrowing (reverse insertion order)
     - `test_remove_pattern_forcing_merge`: Forces node merging
     - `test_remove_interleaved_pattern`: Tests interleaved insertion followed by sequential removal
     - `test_deep_tree_removal`: Tests height-4 tree with 63 elements
     - `test_partial_removal_patterns`: Partial removal with validation
     - `test_specific_underflow_sequence`: Tests specific key patterns
3. **Property-based tests**: Uses `proptest` to test random inputs
   - `test_uints`: Tests with random u32 key-value pairs
   - `test_strings`: Tests with random string keys
   - `test_removal_operations`: Random insertions followed by removals via `first_entry()` - enhanced with detailed diagnostics
   - `test_removal_operations_old`: Original version kept for comparison
4. **Allocation verification**: Uses `CountingAllocator` to ensure no memory leaks
   - All tests verify `net_allocations() == 0` after drop

When adding features, follow the existing test pattern: write explicit tests for edge cases, then add property-based tests for randomized validation.

### Bug History

**Compressed B-Tree - Fixed Bugs**:
1. ✅ **Underflow check condition**: `OccupiedEntry::remove_entry()` was using `if true` instead of `if check_underflow` when deciding whether to check for root reduction (src/compressed/entry.rs:170)
2. ✅ **Right-sibling borrowing**: When borrowing from right sibling during underflow, was incorrectly using `insert_first_entry()` instead of `insert_last_entry()`, violating B-tree ordering (src/compressed/node/interior_node.rs:624)
3. ✅ **Interior node merge**: `InteriorNode::merge()` was only copying `n_keys` children instead of `n_keys + 1`, losing the last child pointer (src/compressed/node/interior_node.rs:538-543)

**Naive B-Tree - Fixed Bugs**:
1. ✅ **Interior node merge (incomplete children copy)**: `Node::_merge()` was only copying `rhs.n_keys` children instead of `rhs.n_keys + 1`, losing the last child pointer. This is the same bug as #3 in compressed B-tree. (src/btree/node.rs:587-593)
2. ✅ **Leaf node merge (stale children)**: When merging leaf nodes, the unified `Node` struct had stale `Some` values in the children array from previous operations. Fixed by explicitly setting all children to `None` for leaf node merges. (src/btree/node.rs:595-598)
3. ✅ **Root reduction on empty leaf**: `OccupiedEntry::remove_entry()` tried to reduce tree height when root had 0 keys, even if root was an empty leaf node (no children). Fixed by only reducing height if `root.child_at(0).is_some()`. (src/btree/entry.rs:173-177)

**All Known Issues Resolved**: Both implementations now pass all tests including proptests with 1000+ cases.

## Dependencies

- `allocated` (path dependency to sibling crate) - Core allocator pattern
- `allocator-api2` - Allocator trait (for stable Rust compatibility)
- `generic-array` + `typenum` - Compile-time sized arrays
- `proptest` (dev) - Property-based testing
- `itertools` (dev) - Test assertions
