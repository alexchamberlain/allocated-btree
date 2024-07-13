//! Demonstrates the ergonomic wrapper types for B-Trees.
//!
//! This example shows how to use the safe wrapper types (`NaiveBTreeMap` and
//! `CompressedBTreeMap`) instead of the lower-level allocated types.

use allocated_btree::{CompressedBTreeMap, NaiveBTreeMap};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Naive B-Tree Demo ===\n");
    naive_btree_demo()?;

    println!("\n=== Compressed B-Tree Demo ===\n");
    compressed_btree_demo()?;

    Ok(())
}

fn naive_btree_demo() -> Result<(), Box<dyn std::error::Error>> {
    // Create a new B-Tree using the ergonomic wrapper
    let mut map = NaiveBTreeMap::new();

    // Insert some key-value pairs (no unsafe blocks needed!)
    map.insert(3, "three")?;
    map.insert(1, "one")?;
    map.insert(4, "four")?;
    map.insert(1, "ONE")?; // Updates existing key
    map.insert(5, "five")?;
    map.insert(9, "nine")?;
    map.insert(2, "two")?;

    println!("Inserted {} items", map.len());

    // Query the map
    if let Some(value) = map.get(&1) {
        println!("Key 1: {}", value);
    }

    // Iterate over entries (sorted by key)
    println!("\nAll entries:");
    for (k, v) in &map {
        println!("  {} -> {}", k, v);
    }

    // Use the entry API for in-place manipulation
    let entry = map.entry(6);
    entry.insert("six")?;

    println!("\nAfter adding 6: {} items", map.len());

    // Remove an entry
    if let Some(entry) = map.first_entry() {
        let (k, v) = entry.remove_entry();
        println!("\nRemoved first entry: {} -> {}", k, v);
    }

    println!("Final count: {} items", map.len());

    Ok(())
}

fn compressed_btree_demo() -> Result<(), Box<dyn std::error::Error>> {
    // The compressed B-Tree has the same API but uses ~50% less memory
    let mut map = CompressedBTreeMap::new();

    // Insert some data
    for i in 0..10 {
        map.insert(i, i * i)?;
    }

    println!("Inserted {} items", map.len());

    // Check if a key exists
    if map.contains_key(&5) {
        println!("Key 5 exists with value: {}", map.get(&5).unwrap());
    }

    // Modify a value
    if let Some(value) = map.get_mut(&3) {
        *value = 100;
        println!("Updated key 3 to 100");
    }

    // Iterate over just the keys
    print!("\nKeys: ");
    for k in map.keys() {
        print!("{} ", k);
    }
    println!();

    // Clear all entries
    map.clear()?;
    println!("\nAfter clear: {} items", map.len());

    Ok(())
}
