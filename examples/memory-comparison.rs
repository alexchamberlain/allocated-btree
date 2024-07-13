//! Demonstrates memory usage comparison between naive and compressed B-Trees.
//!
//! This example shows the memory savings achieved by the compressed implementation
//! by tracking allocations for both implementations with the same dataset.

use allocated::CountingAllocator;
use allocated_btree::{AllocatedCompressedBTreeMap, AllocatedNaiveBTreeMap};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== B-Tree Memory Comparison ===\n");

    // Test with different sizes
    for size in [10, 100, 1000, 10000] {
        compare_implementations(size)?;
    }

    Ok(())
}

fn compare_implementations(n: usize) -> Result<(), Box<dyn std::error::Error>> {
    // Naive B-Tree with counting allocator
    let naive_alloc = CountingAllocator::default();
    let mut naive_map = AllocatedNaiveBTreeMap::<u64, u64>::new_in(&naive_alloc)?;

    for i in 0..n {
        unsafe {
            naive_map.insert_in(&naive_alloc, i as u64, i as u64 * 2)?;
        }
    }

    let naive_allocations = naive_alloc.n_allocations();
    let naive_bytes = naive_alloc.n_bytes_allocated();

    // Drop the naive map to clean up
    std::mem::drop(naive_map);
    assert_eq!(naive_alloc.net_allocations(), 0, "Naive map leaked memory");

    // Compressed B-Tree with counting allocator
    let compressed_alloc = CountingAllocator::default();
    let mut compressed_map = AllocatedCompressedBTreeMap::<u64, u64>::new_in(&compressed_alloc)?;

    for i in 0..n {
        unsafe {
            compressed_map.insert_in(&compressed_alloc, i as u64, i as u64 * 2)?;
        }
    }

    let compressed_allocations = compressed_alloc.n_allocations();
    let compressed_bytes = compressed_alloc.n_bytes_allocated();

    // Drop the compressed map
    std::mem::drop(compressed_map);
    assert_eq!(
        compressed_alloc.net_allocations(),
        0,
        "Compressed map leaked memory"
    );

    // Calculate savings
    let bytes_saved = naive_bytes.saturating_sub(compressed_bytes);
    let savings_percent = if naive_bytes > 0 {
        (bytes_saved as f64 / naive_bytes as f64) * 100.0
    } else {
        0.0
    };

    println!("Dataset size: {} entries", n);
    println!("  Naive:");
    println!("    Allocations: {}", naive_allocations);
    println!("    Bytes:       {}", naive_bytes);
    println!("  Compressed:");
    println!("    Allocations: {}", compressed_allocations);
    println!("    Bytes:       {}", compressed_bytes);
    println!("  Savings:");
    println!("    Bytes:       {} ({:.1}%)", bytes_saved, savings_percent);
    println!();

    Ok(())
}
