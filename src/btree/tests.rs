#![allow(
    clippy::undocumented_unsafe_blocks,
    clippy::multiple_unsafe_ops_per_block
)]

extern crate alloc;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use core::mem::size_of;
use std::error::Error;

use proptest::prelude::*;

use itertools::assert_equal;
use itertools::Itertools;

use allocated::{CollectIn, CountingAllocator};

use super::*;

#[test]
fn test_constructor() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        assert_eq!(btree.n, 0);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![]);

        assert_eq!(btree.len(), 0);
        assert!(btree.is_empty());

        assert!(!btree.contains_key(&1));
        assert_eq!(btree.get(&1), None);

        assert!(btree.first_entry_in(&alloc).is_none());
        assert_eq!(btree.first_key_value(), None);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 0);

    Ok(())
}

#[test]
fn test_one() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;

        assert_eq!(btree.n, 1);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1)]);

        assert_eq!(btree.len(), 1);
        assert!(!btree.is_empty());

        assert!(btree.contains_key(&1));
        assert_eq!(btree.get(&1), Some(&1));

        let entry = btree.first_entry_in(&alloc).unwrap();
        assert_eq!(entry.key(), &1);
        assert_eq!(entry.get(), &1);

        assert_eq!(btree.first_key_value(), Some((&1, &1)));

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 0);

    Ok(())
}

#[test]
fn test_3_in_order() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9)],
        );

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 0);

    Ok(())
}

#[test]
fn test_3_out_of_order() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 2, 4)?;

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9)],
        );

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 0);

    Ok(())
}

#[test]
fn test_12() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        for i in 1..=12 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 12);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=12).map(|i| (i, i * i)),
        );

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 0);

    Ok(())
}

#[test]
fn test_13() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        for i in 1..=13 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 13);

        assert_eq!(btree.root.as_ref().unwrap().n_keys(), 1);
        assert_eq!(*btree.root.as_ref().unwrap().key_at(0), 7);
        assert_eq!(*btree.root.as_ref().unwrap().value_at(0), 49);

        let lhn = btree.root.as_ref().unwrap().child_at(0);
        assert!(lhn.is_some());
        let lhn: &Node<_, _, _> = lhn.unwrap().as_ref();
        assert_eq!(lhn.n_keys(), 6);

        let rhn = btree.root.as_ref().unwrap().child_at(1);
        assert!(rhn.is_some());
        let rhn: &Node<_, _, _> = rhn.unwrap().as_ref();
        assert_eq!(rhn.n_keys(), 6);

        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=13).map(|i| (i, i * i)),
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 2);

    Ok(())
}

#[test]
fn test_14() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32>::new_in(&alloc)?;

    unsafe {
        for i in 1..=14 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 14);

        assert_eq!(btree.root.as_ref().unwrap().n_keys(), 1);
        assert_eq!(*btree.root.as_ref().unwrap().key_at(0), 7);
        assert_eq!(*btree.root.as_ref().unwrap().value_at(0), 49);

        let lhn = btree.root.as_ref().unwrap().child_at(0);
        assert!(lhn.is_some());
        let lhn: &Node<_, _, _> = lhn.unwrap().as_ref();
        assert_eq!(lhn.n_keys(), 6);

        let rhn = btree.root.as_ref().unwrap().child_at(1);
        assert!(rhn.is_some());
        let rhn: &Node<_, _, _> = rhn.unwrap().as_ref();
        assert_eq!(rhn.n_keys(), 7);

        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=14).map(|i| (i, i * i)),
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U6>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_1() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;

        assert_eq!(btree.n, 1);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_1_twice() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        let v = btree.insert_in(&alloc, 1, 1)?;
        assert_eq!(v, None);
        let v = btree.insert_in(&alloc, 1, 2)?;
        assert_eq!(v, Some(1));

        assert_eq!(btree.n, 1);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 2)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_2() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;

        assert_eq!(btree.n, 2);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1), (2, 4)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_3() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_into_iter() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;

        assert_eq!(btree.n, 3);
        assert_equal(
            ManuallyDrop::into_inner(btree.into_inner()).into_iter_in(&alloc),
            vec![(1, 1), (2, 4), (3, 9)],
        );
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_twice() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        let v = btree.insert_in(&alloc, 2, 4)?;
        assert_eq!(v, None);
        btree.insert_in(&alloc, 3, 9)?;

        let v = btree.insert_in(&alloc, 2, 8)?;
        assert_eq!(v, Some(4));

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 8), (3, 9)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_lhs() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 1, 1)?;

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9)],
        );

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_7_insert() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        for i in 1..=7 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 7);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=7).map(|i| (i, i * i)),
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 6);

    Ok(())
}

#[test]
fn test_small_7_collect_in() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        (1..=7).map(|k| (k, k * k)).collect_in(&alloc)?;

    assert_eq!(btree.n, 7);
    assert_equal(
        btree.iter().map(|(k, v)| (*k, *v)),
        (1..=7).map(|i| (i, i * i)),
    );

    core::mem::drop(btree);

    _assert_allocations::<_, U1>(alloc, 6);

    Ok(())
}

#[test]
fn test_small_7_get() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        (1..=7).map(|k| (k, k * k)).collect_in(&alloc)?;

    for i in 1..=7 {
        assert_eq!(*btree.get(&i).unwrap(), i * i);
    }

    core::mem::drop(btree);
    _assert_allocations::<_, U1>(alloc, 6);

    Ok(())
}

#[test]
fn test_small_7_clear_in() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        (1..=7).map(|k| (k, k * k)).collect_in(&alloc)?;

    unsafe {
        btree.clear_in(&alloc)?;
    }

    assert!(btree.is_empty());

    core::mem::drop(btree);
    _assert_allocations::<_, U1>(alloc, 6);

    Ok(())
}

#[test]
fn test_small_1_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // btree.insert_in(&alloc, 1, 1)?;
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(1)?;
            }
        }

        assert_eq!(btree.n, 1);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_1_twice_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // let v = btree.insert_in(&alloc, 1, 1)?;
        // assert_eq!(v, None);
        // let v = btree.insert_in(&alloc, 1, 2)?;
        // assert_eq!(v, Some(1));
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(1)?;
            }
        }
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(mut o) => {
                assert_eq!(o.insert(2), 1);
            }
            Entry::Vacant(_v) => {
                panic!("Expected occupied");
            }
        }

        assert_eq!(btree.n, 1);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 2)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_2_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // btree.insert_in(&alloc, 1, 1)?;
        // btree.insert_in(&alloc, 2, 4)?;
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(1)?;
            }
        }
        let entry = btree.entry_in(&alloc, 2);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(4)?;
            }
        }

        assert_eq!(btree.n, 2);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1), (2, 4)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_2_entry_remove() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(o) => {
                assert_eq!(o.remove(), 1);
            }
            Entry::Vacant(_v) => {
                panic!("Expected occupied");
            }
        }

        assert_eq!(btree.n, 1);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(2, 4)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

#[test]
fn test_small_3_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // btree.insert_in(&alloc, 1, 1)?;
        // btree.insert_in(&alloc, 2, 4)?;
        // btree.insert_in(&alloc, 3, 9)?;
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(1)?;
            }
        }
        let entry = btree.entry_in(&alloc, 2);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(4)?;
            }
        }
        let entry = btree.entry_in(&alloc, 3);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(9)?;
            }
        }

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_entry_remove_1() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;

        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(o) => {
                // panic!("Expected vacant");
                assert_eq!(o.remove(), 1);
            }
            Entry::Vacant(_v) => {
                panic!("Expected occupied");
            }
        }

        assert_eq!(btree.n, 2);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(2, 4), (3, 9)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_entry_remove_2() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;

        let entry = btree.entry_in(&alloc, 2);
        match entry {
            Entry::Occupied(o) => {
                assert_eq!(o.remove(), 4);
            }
            Entry::Vacant(_v) => {
                panic!("Expected occupied");
            }
        }

        assert_eq!(btree.n, 2);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1), (3, 9)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_entry_remove_3() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;

        let entry = btree.entry_in(&alloc, 3);
        match entry {
            Entry::Occupied(o) => {
                assert_eq!(o.remove(), 9);
            }
            Entry::Vacant(_v) => {
                panic!("Expected occupied");
            }
        }

        assert_eq!(btree.n, 2);
        assert_equal(btree.iter().map(|(k, v)| (*k, *v)), vec![(1, 1), (2, 4)]);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_twice_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(1)?;
            }
        }
        let entry = btree.entry_in(&alloc, 2);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(4)?;
            }
        }
        let entry = btree.entry_in(&alloc, 3);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(9)?;
            }
        }
        let entry = btree.entry_in(&alloc, 2);
        match entry {
            Entry::Occupied(mut o) => {
                assert_eq!(o.insert(8), 4);
            }
            Entry::Vacant(_v) => {
                panic!("Expected occupied");
            }
        }

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 8), (3, 9)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_3_lhs_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        let entry = btree.entry_in(&alloc, 2);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(4)?;
            }
        }
        let entry = btree.entry_in(&alloc, 3);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(9)?;
            }
        }
        let entry = btree.entry_in(&alloc, 1);
        match entry {
            Entry::Occupied(_o) => {
                panic!("Expected vacant");
            }
            Entry::Vacant(v) => {
                v.insert(1)?;
            }
        }

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9)],
        );

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_7_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        for i in 1..=7 {
            // btree.insert_in(&alloc, i, i * i)?;
            let entry = btree.entry_in(&alloc, i);
            match entry {
                Entry::Occupied(_o) => {
                    panic!("Expected vacant");
                }
                Entry::Vacant(v) => {
                    v.insert(i * i)?;
                }
            }
        }

        assert_eq!(btree.n, 7);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=7).map(|i| (i, i * i)),
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 6);

    Ok(())
}

#[test]
fn test_small_5_ooo() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 4, 16)?;

        assert_eq!(btree.n, 5);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=5).map(|i| (i, i * i)),
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_4_ooo_remove_3() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;

        let o = btree.entry_in(&alloc, 3);
        assert_eq!(o.unwrap_occupied().remove(), 9);

        assert_eq!(btree.n, 3);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (5, 25)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_6_ooo_remove_1_lhs() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 6, 36)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 1);
        assert_eq!(o.unwrap_occupied().remove(), 1);

        assert_eq!(btree.n, 5);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(2, 4), (3, 9), (4, 16), (5, 25), (6, 36)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 3);

    Ok(())
}

#[test]
fn test_small_6_ooo_remove_6_lhs() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 6, 36)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 6);
        assert_eq!(o.unwrap_occupied().remove(), 36);

        assert_eq!(btree.n, 5);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9), (4, 16), (5, 25)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 3);

    Ok(())
}

#[test]
fn test_small_5_ooo_remove_1() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 1);
        assert_eq!(o.unwrap_occupied().remove(), 1);

        assert_eq!(btree.n, 4);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(2, 4), (3, 9), (4, 16), (5, 25)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_5_ooo_remove_2() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 2);
        assert_eq!(o.unwrap_occupied().remove(), 4);

        assert_eq!(btree.n, 4);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (3, 9), (4, 16), (5, 25)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_5_ooo_remove_3() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 3);
        assert_eq!(o.unwrap_occupied().remove(), 9);

        assert_eq!(btree.n, 4);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (4, 16), (5, 25)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_5_ooo_remove_4() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 4);
        assert_eq!(o.unwrap_occupied().remove(), 16);

        assert_eq!(btree.n, 4);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9), (5, 25)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_5_ooo_remove_5() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, 1, 1)?;
        btree.insert_in(&alloc, 3, 9)?;
        btree.insert_in(&alloc, 5, 25)?;
        btree.insert_in(&alloc, 2, 4)?;
        btree.insert_in(&alloc, 4, 16)?;

        let o = btree.entry_in(&alloc, 5);
        assert_eq!(o.unwrap_occupied().remove(), 25);

        assert_eq!(btree.n, 4);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            vec![(1, 1), (2, 4), (3, 9), (4, 16)],
        );

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 2);

    Ok(())
}

#[test]
fn test_small_7_first_entry() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        for i in 1..=7 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 7);
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (1..=7).map(|i| (i, i * i)),
        );

        let entry = btree.first_entry_in(&alloc);

        assert!(entry.is_some());

        let entry = entry.unwrap();
        assert_eq!(*entry.key(), 1);
        assert_eq!(*entry.get(), 1);

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 6);

    Ok(())
}

#[test]
fn test_small_strings() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<String, String, U1>::new_in(&alloc)?;

    unsafe {
        btree.insert_in(&alloc, "hello".to_string(), "world".to_string())?;

        assert_eq!(btree.n, 1);

        let entry = btree.first_entry_in(&alloc);

        assert!(entry.is_some());

        let entry = entry.unwrap();
        assert_eq!(entry.key(), "hello");
        assert_eq!(entry.get(), "world");

        btree.drop_in(&alloc);

        core::mem::forget(btree);
    }

    _assert_allocations::<_, U1>(alloc, 0);

    Ok(())
}

// {
//     887: 135,
//     261: 164,
//     120: 399,
//     225: 597,
//     600: 849,
// }

#[test]
fn test_uints_failure_1() -> Result<(), Box<dyn Error>> {
    let data = [(887, 135), (261, 164), (120, 399), (225, 597), (600, 849)];

    let alloc = CountingAllocator::default();
    // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
    let btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        data.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;

    assert_eq!(btree.len(), data.len());

    core::mem::drop(btree);

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_uints_failure_2() -> Result<(), Box<dyn Error>> {
    let data = [(0, 0), (601, 0), (1, 0)];

    let alloc = CountingAllocator::default();
    // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
    let btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        data.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;

    assert_eq!(btree.len(), data.len());

    core::mem::drop(btree);

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_uints_failure_3() -> Result<(), Box<dyn Error>> {
    let data = [(327, 0), (0, 0), (328, 0), (1, 0), (2, 0)];

    let alloc = CountingAllocator::default();
    // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
    let btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        data.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;

    assert_eq!(btree.len(), data.len());

    core::mem::drop(btree);

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_uints_failure_4() -> Result<(), Box<dyn Error>> {
    let data = [
        (598, 0),
        (0, 0),
        (405, 0),
        (1, 0),
        (613, 0),
        (614, 0),
        (599, 0),
        (406, 0),
        // (2, 0),
        // (3, 0),
        // (4, 0),
        // (406, 0),
        // (0, 0),
        // (0, 0),
        // (0, 0),
    ];

    let alloc = CountingAllocator::default();
    // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
    let btree: DropGuard<AllocatedBTreeMap<u32, u32, U1>, _> =
        data.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;

    let mut data: Vec<_> = data.into_iter().collect();
    data.push((406, 0));
    data.sort_by(|a, b| a.0.cmp(&b.0));
    let data: Vec<_> = data.into_iter().unique_by(|v| v.0).collect();

    assert_equal(btree.iter().map(|(k, v)| (*k, *v)), data.iter().copied());

    assert_eq!(btree.len(), data.len());

    core::mem::drop(btree);

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_uints_failure_loads() -> Result<(), Box<dyn Error>> {
    let data = [
        (3856925184, 0),
        (3402180436, 0),
        (2985096347, 0),
        (1925598998, 0),
        (3994432415, 0),
        (3568182477, 0),
        (422324889, 0),
        (3279466799, 0),
        (834491844, 0),
        (1217548835, 0),
        (1068474374, 0),
        (283834474, 0),
        (13861378, 0),
        (2089785859, 0),
        (3580583242, 0),
        (259396938, 0),
        (3868055674, 0),
        (2815329951, 0),
        (664617067, 0),
        (221253782, 0),
        (2337103507, 0),
        (3070955222, 0),
        (3927666144, 0),
        (2591442572, 0),
        (1527221349, 0),
        (712102085, 0),
        (1585665407, 0),
        (1366235977, 0),
        (650424938, 0),
        (3083591870, 0),
        (4272581846, 0),
        (2424156845, 0),
        (1686214660, 0),
        (3465267022, 0),
        (1875993905, 0),
        (118049930, 0),
        (473214280, 0),
        (2528605557, 0),
        (3928545697, 0),
        (3014146819, 0),
        (1241008516, 0),
        (2642385749, 0),
        (150373831, 0),
        (665951480, 0),
        (1284265938, 0),
        (193327118, 0),
        (3412299425, 0),
        (285817681, 0),
        (4111021481, 0),
        (1878210083, 0),
        (3296311277, 0),
        (1898733543, 0),
        (1938171018, 0),
        (301566170, 0),
        (968417, 0),
        (2054929847, 0),
        (3158528533, 0),
        (964653677, 0),
        (2320121809, 0),
        (3053839295, 0),
        (1275906398, 0),
        (82502578, 0),
        (2114388733, 0),
        (3425667474, 0),
        (3984609531, 0),
        (1205699104, 0),
        (730789824, 0),
        (3452436427, 0),
        (726043677, 0),
        (2308991188, 0),
        (2051810140, 0),
        (91875063, 0),
        (2362021834, 0),
        (3420025975, 0),
        (599978792, 0),
        (2800049234, 0),
        (2401522216, 0),
        (2299790801, 0),
        (619012682, 0),
        (4281714447, 0),
        (711823189, 0),
        (3770014394, 0),
        (570319656, 0),
        (1262825459, 0),
        (276105090, 0),
        (3231446937, 0),
        (1321077540, 0),
        (260430536, 0),
        (1986471891, 0),
        (1919659776, 0),
        (2829097072, 0),
        (1846625795, 0),
        (2717784472, 0),
        (4110686552, 0),
        (1591362573, 0),
        (1660182128, 0),
        (1659517004, 0),
        (3997176083, 0),
        (3721855058, 0),
        (1192104735, 0),
        (1931312466, 0),
        (3890938834, 0),
        (2676195993, 0),
        (2211494870, 0),
        (1086163178, 0),
        (1272652623, 0),
        (2657203628, 0),
        (3678942879, 0),
        (1686096325, 0),
        (4037301010, 0),
        (2830561555, 0),
        (3743861889, 0),
        (1240214536, 0),
        (3722320874, 0),
        (1018427735, 0),
        (1956901705, 0),
        (920458329, 0),
        (2418304359, 0),
        (3981019963, 0),
        (3073339283, 0),
        (3851057034, 0),
        (975488044, 0),
        (877310946, 0),
        (2616586561, 0),
        (136993547, 0),
        (3521298252, 0),
        (2573667317, 0),
        (3264258209, 0),
        (843241601, 0),
        (3644601479, 0),
        (480770138, 0),
        (4134592911, 0),
        (3196390085, 0),
        (3720919772, 0),
        (3313146818, 0),
        (2674153209, 0),
        (1943751723, 0),
        (3422375926, 0),
        (4034335710, 0),
        (1851252191, 0),
        (1431372296, 0),
        (3181853376, 0),
        (866612689, 0),
        (2580060964, 0),
        (2063956353, 0),
        (3299617048, 0),
        (2598411978, 0),
        (711281401, 0),
        (2553764125, 0),
        (1292341336, 0),
        (603356954, 0),
        (4087197404, 0),
        (2995061837, 0),
        (3386807899, 0),
        (1868378154, 0),
        (2616660582, 0),
        (1514280764, 0),
        (1641374668, 0),
        (2011909817, 0),
        (2473477839, 0),
        (340436548, 0),
        (1822666094, 0),
        (3721893503, 0),
        (949386811, 0),
        (3864268537, 0),
        (2311618439, 0),
        (32837310, 0),
        (2551862903, 0),
        (3314830743, 0),
        (2660366809, 0),
        (4261657676, 0),
        (3006667254, 0),
        (1743185393, 0),
        (3442633658, 0),
        (338341103, 0),
        (932113585, 0),
        (486142805, 0),
        (439917374, 0),
        (1860706079, 0),
        (4127219227, 0),
        (330720182, 0),
        (1553020817, 0),
        (2048213724, 0),
        (3266552250, 0),
        (961371819, 0),
        (1320340146, 0),
        (208968101, 0),
        (952184070, 0),
        (455764076, 0),
        (130147460, 0),
        (3486797624, 0),
        (3588947435, 0),
        (2844975184, 0),
        (888992572, 0),
        (3356400152, 0),
        (2415420148, 0),
        (4194374062, 0),
        (1537843780, 0),
        (3948123576, 0),
        (1802384313, 0),
        (869229702, 0),
        (2107136303, 0),
        (2608731522, 0),
        (390642644, 0),
        (3402929798, 0),
        (3498082418, 0),
        (4009170078, 0),
        (1926481918, 0),
        (1579630815, 0),
        (3061860463, 0),
        (3774924262, 0),
        (3323851637, 0),
        (953376214, 0),
        (1638594407, 0),
        (348362967, 0),
        (3615911163, 0),
        (3012001174, 0),
        (984025367, 0),
        (1473949700, 0),
        (3585517993, 0),
        (577259632, 0),
        (132704292, 0),
        (321236395, 0),
        (3018428214, 0),
        (24700090, 0),
        (1826416509, 0),
        (793734547, 0),
        (1334899843, 0),
        (1187105163, 0),
        (1194665100, 0),
        (4046848058, 0),
        (2836640147, 0),
        (178190546, 0),
        (1208676897, 0),
        (3991202176, 0),
        (425149853, 0),
        (2462568938, 0),
        (4187480617, 0),
        (2930032342, 0),
        (1456479204, 0),
        (205716085, 0),
        (859628185, 0),
        (2500630233, 0),
        (771795719, 0),
        (1867034962, 0),
        (1974514376, 0),
        (1827124896, 0),
        (4069868245, 0),
        (3323015065, 0),
        (2156039625, 0),
        (1995938921, 0),
        (651689477, 0),
        (1095494114, 0),
        (1284113094, 0),
        (3045273250, 0),
        (3563416770, 0),
        (3766731176, 0),
        (3255261036, 0),
        (318619370, 0),
        (441855795, 0),
        (78420196, 0),
        (3305593725, 0),
        (3068834675, 0),
        (3888181984, 0),
        (1402766149, 0),
        (1868621603, 0),
        (2710396261, 0),
        (433439521, 0),
        (3999388030, 0),
        (1953413698, 0),
        (921722045, 0),
        (1141887443, 0),
        (4270240545, 0),
        (1006006120, 0),
        (1673967561, 0),
        (582970338, 0),
        (20734442, 0),
        (724419837, 0),
        (1966180816, 0),
        (594721452, 0),
        (3438142300, 0),
        (1105054460, 0),
        (2557257942, 0),
        (785004409, 0),
        (3750296135, 0),
        (1051564844, 0),
        (2662911446, 0),
        (641215560, 0),
        (4090625979, 0),
        (2086027679, 0),
        (3724538074, 0),
        (4222889874, 0),
        (2953906324, 0),
        (2539250840, 0),
        (2060502583, 0),
        (3862854187, 0),
        (3071694085, 0),
        (3453734909, 0),
        (4278388560, 0),
        (266558530, 0),
        (4159041854, 0),
        (1562044264, 0),
        (2327485256, 0),
        (2790452392, 0),
        (2955727362, 0),
        (2360873227, 0),
        (2057665976, 0),
        (266429960, 0),
        (94192970, 0),
        (2845279075, 0),
        (805400792, 0),
        (1387940901, 0),
        (789599265, 0),
        (1508307896, 0),
        (265569449, 0),
        (705210419, 0),
        (2675986306, 0),
        (2670464656, 0),
        (2417452985, 0),
        (3563049599, 0),
        (1206842802, 0),
        (616356409, 0),
        (2329842332, 0),
        (664853390, 0),
        (4023064475, 0),
        (302683529, 0),
        (1160570562, 0),
        (1822202791, 0),
        (412399968, 0),
        (3261769773, 0),
        (4284089972, 0),
        (636751848, 0),
        (1284007784, 0),
        (1134252379, 0),
        (1493606214, 0),
        (2792193336, 0),
        (2148981816, 0),
        (2756775323, 0),
        (2323536581, 0),
        (2356163742, 0),
        (1330302005, 0),
        (3307354775, 0),
        (16607277, 0),
        (414731591, 0),
        (136949794, 0),
        (4261106769, 0),
        (4160913442, 0),
        (4208875757, 0),
        (1302279562, 0),
        (3546341172, 0),
        (453223866, 0),
        (2774231117, 0),
        (1267146368, 0),
        (207556684, 0),
        (1201620918, 0),
        (3970893834, 0),
        (3740286590, 0),
        (178095893, 0),
        (1367061086, 0),
        (1307461098, 0),
        (1461314834, 0),
        (3986730471, 0),
        (1051352765, 0),
        (1118514920, 0),
        (304791662, 0),
        (3372588493, 0),
        (1067330017, 0),
        (934122081, 0),
        (1580461025, 0),
        (3429150662, 0),
        (1873402169, 0),
        (117309184, 0),
        (1374842056, 0),
        (1660335287, 0),
        (3863317722, 0),
        (3743214156, 0),
        (1430655460, 0),
        (287051718, 0),
        (3012137154, 0),
        (1664597508, 0),
        (4220548985, 0),
        (449857620, 0),
        (3400731418, 0),
        (3027183544, 0),
        (1562427958, 0),
        (2928382017, 0),
        (2083888940, 0),
        (4275579916, 0),
        (1426082440, 0),
        (3254242579, 0),
        (2773025477, 0),
        (3082035419, 0),
        (3168799984, 0),
        (722149491, 0),
        (4079454489, 0),
        (2951495595, 0),
        (4135885514, 0),
        (1259821951, 0),
        (949216248, 0),
        (1587094393, 0),
        (2182482850, 0),
        (3477444853, 0),
        (2447069788, 0),
        (236615922, 0),
        (1886945655, 0),
        (3307881054, 0),
        (2671185702, 0),
        (74898734, 0),
        (2530786187, 0),
        (3364844355, 0),
        (3641086429, 0),
        (4043235958, 0),
        (2218851552, 0),
        (4018860175, 0),
        (2203610424, 0),
        (122106283, 0),
        (1024588414, 0),
        (3446294268, 0),
        (840482710, 0),
        (3471093797, 0),
        (4289331425, 0),
        (3890214363, 0),
        (1471952101, 0),
        (2071048248, 0),
        (3890257925, 0),
    ];

    let alloc = CountingAllocator::default();
    // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
    let btree: DropGuard<AllocatedBTreeMap<u32, u32>, _> =
        data.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;

    let mut data: Vec<_> = data.into_iter().collect();
    data.sort_by(|a, b| a.0.cmp(&b.0));
    let data: Vec<_> = data.into_iter().unique_by(|v| v.0).collect();

    // assert_equal(btree.iter().map(|(k, v)| (*k, *v)), data.iter().copied());

    assert_eq!(btree.len(), data.len());

    core::mem::drop(btree);

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

proptest! {
    #[test]
    fn test_uints(mut map in prop::collection::vec((0..1000u32, 0..1000u32), 1..100)) {
        let alloc = CountingAllocator::default();
        // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
        // let btree: DropGuard::<AllocatedBTreeMap::<u32, u32, U1>, _> = map.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;
        let btree: DropGuard::<AllocatedBTreeMap::<u32, u32, U1>, _> = map.iter().copied().collect_in(&alloc)?;

        map.sort_by(|a, b| a.0.cmp(&b.0));
        let map: Vec<_> = map.into_iter().unique_by(|v| v.0).collect();

        assert_eq!(btree.len(), map.len());

        core::mem::drop(btree);

        assert_eq!(alloc.net_allocations(), 0);
        assert_eq!(alloc.net_bytes_allocated(), 0);
    }
}

proptest! {
    #[test]
    fn test_strings(mut map in prop::collection::vec(".*", 1..100)) {
        let alloc = CountingAllocator::default();
        // let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
        // let btree: DropGuard::<AllocatedBTreeMap::<u32, u32, U1>, _> = map.iter().map(|(k, v)| (*k, *v)).collect_in(&alloc)?;
        let btree: DropGuard::<AllocatedBTreeMap::<String, (), U1>, _> = map.iter().map(|s| (s.clone(), ())).collect_in(&alloc)?;

        map.sort();
        let map: Vec<_> = map.into_iter().unique().collect();

        assert_eq!(btree.len(), map.len());

        core::mem::drop(btree);

        assert_eq!(alloc.net_allocations(), 0);
        assert_eq!(alloc.net_bytes_allocated(), 0);
    }
}

// Tests for underflow handling edge cases (mirroring compressed B-tree tests)
#[test]
fn test_remove_simple_5() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // With B=1, inserting 5 elements should create a tree with splits
        for i in 0..5 {
            btree.insert_in(&alloc, i, i)?;
        }

        // Remove all elements
        for expected in 0..5 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            let (k, v) = entry.remove_entry();
            assert_eq!(k, expected);
            assert_eq!(v, expected);
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_all_8_elements() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        for i in 0..8 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 8);

        // Remove all elements using first_entry
        for expected_key in 0..8 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), expected_key);
            let (k, v) = entry.remove_entry();
            assert_eq!(k, expected_key);
            assert_eq!(v, expected_key * expected_key);
        }

        assert_eq!(btree.n, 0);
        assert!(btree.is_empty());

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_all_15_elements() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        for i in 0..15 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 15);

        // Remove all elements using first_entry
        for expected_key in 0..15 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), expected_key);
            let (k, v) = entry.remove_entry();
            assert_eq!(k, expected_key);
            assert_eq!(v, expected_key * expected_key);
        }

        assert_eq!(btree.n, 0);
        assert!(btree.is_empty());

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_all_31_elements() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        for i in 0..31 {
            btree.insert_in(&alloc, i, i * i)?;
        }

        assert_eq!(btree.n, 31);

        // Remove all elements using first_entry - this creates a 3-level tree
        for expected_key in 0..31 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), expected_key);
            let (k, v) = entry.remove_entry();
            assert_eq!(k, expected_key);
            assert_eq!(v, expected_key * expected_key);
        }

        assert_eq!(btree.n, 0);
        assert!(btree.is_empty());

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_pattern_causing_left_borrow() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Create a specific tree structure that will force left sibling borrowing
        for i in 0..7 {
            btree.insert_in(&alloc, i, i)?;
        }

        // Remove element that causes underflow requiring left borrow
        for _ in 0..7 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_pattern_causing_right_borrow() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Insert in reverse order to create different tree structure
        for i in (0..7).rev() {
            btree.insert_in(&alloc, i, i)?;
        }

        // Remove from beginning
        for _ in 0..7 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_pattern_forcing_merge() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Create specific pattern that forces node merging
        for i in 0..5 {
            btree.insert_in(&alloc, i, i)?;
        }

        // Remove elements to force merge operations
        for _ in 0..5 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_remove_interleaved_pattern() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Insert interleaved pattern
        let keys = [0, 4, 2, 6, 1, 5, 3, 7];
        for &k in &keys {
            btree.insert_in(&alloc, k, k)?;
        }

        // Remove all from beginning
        for expected in 0..8 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), expected);
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_deep_tree_removal() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Create a deeper tree (height 4) with 63 elements
        for i in 0..63 {
            btree.insert_in(&alloc, i, i)?;
        }

        // Remove all elements
        for expected in 0..63 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), expected);
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_partial_removal_patterns() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Insert 20 elements
        for i in 0..20 {
            btree.insert_in(&alloc, i, i)?;
        }

        // Remove first 10
        for expected in 0..10 {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), expected);
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 10);

        // Verify remaining elements
        assert_equal(
            btree.iter().map(|(k, v)| (*k, *v)),
            (10..20).map(|i| (i, i)),
        );

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

#[test]
fn test_specific_underflow_sequence() -> Result<(), Box<dyn Error>> {
    // This test tries to trigger a specific underflow scenario
    let alloc = CountingAllocator::default();
    let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

    unsafe {
        // Build tree with specific structure
        let keys = [10, 20, 5, 15, 25, 3, 7, 12, 17, 22, 27];
        for &k in &keys {
            btree.insert_in(&alloc, k, k)?;
        }

        // Remove in order from beginning
        let expected = [3, 5, 7, 10, 12, 15, 17, 20, 22, 25, 27];
        for &exp in &expected {
            let entry = btree.first_entry_in(&alloc).unwrap();
            assert_eq!(*entry.key(), exp);
            let _ = entry.remove_entry();
        }

        assert_eq!(btree.n, 0);

        btree.drop_in(&alloc);
        core::mem::forget(btree);
    }

    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);

    Ok(())
}

// To reproduce a specific proptest failure:
// 1. When test_removal_operations fails, proptest will print:
//    "minimal failing input: insert_keys = [...], remove_keys = [...]"
// 2. Copy those values into test_removal_operations_reproduce below
// 3. Uncomment and run: cargo test btree::tests::test_removal_operations_reproduce -- --nocapture
//
// #[test]
// fn test_removal_operations_reproduce() -> Result<(), Box<dyn Error>> {
//     // Paste the failing input here:
//     let insert_keys = vec![/* insert_keys from failure */];
//     let remove_keys = vec![/* remove_keys from failure */];
//
//     let alloc = CountingAllocator::default();
//     let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;
//
//     println!("Inserting keys: {:?}", insert_keys);
//     for k in &insert_keys {
//         unsafe {
//             btree.insert_in(&alloc, *k, k * 2)?;
//         }
//     }
//
//     let unique_inserts: std::collections::HashSet<_> = insert_keys.iter().copied().collect();
//     assert_eq!(btree.len(), unique_inserts.len());
//
//     let mut removed_keys = Vec::new();
//     let removals_to_do = remove_keys.len().min(btree.len());
//
//     for i in 0..removals_to_do {
//         println!("\n=== Removal {} ===", i);
//         println!("Tree state before removal:");
//         println!("  Length: {}", btree.len());
//         println!("  Keys: {:?}", btree.iter().map(|(k, _)| *k).collect::<Vec<_>>());
//
//         if let Some(entry) = unsafe { btree.first_entry_in(&alloc) } {
//             let key = *entry.key();
//             println!("  Removing key: {}", key);
//             let (removed_key, removed_value) = entry.remove_entry();
//
//             assert_eq!(removed_key, key);
//             assert_eq!(removed_value, key * 2);
//             removed_keys.push(removed_key);
//
//             println!("Tree state after removal:");
//             println!("  Length: {}", btree.len());
//             println!("  Keys: {:?}", btree.iter().map(|(k, _)| *k).collect::<Vec<_>>());
//         }
//     }
//
//     assert_eq!(btree.len(), unique_inserts.len() - removals_to_do);
//     core::mem::drop(btree);
//     assert_eq!(alloc.net_allocations(), 0);
//     Ok(())
// }

proptest! {
    #[test]
    fn test_removal_operations(
        insert_keys in prop::collection::vec(0..1000u32, 1..100),
        remove_keys in prop::collection::vec(0..1000u32, 0..50)
    ) {
        let alloc = CountingAllocator::default();
        let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

        // Insert all keys
        for k in &insert_keys {
            unsafe {
                btree.insert_in(&alloc, *k, k * 2)?;
            }
        }

        let unique_inserts: std::collections::HashSet<_> = insert_keys.iter().copied().collect();
        assert_eq!(btree.len(), unique_inserts.len(),
            "After insertion, tree length mismatch. insert_keys = {:?}", insert_keys);

        // Remove some keys using first_entry
        let mut removed_keys = Vec::new();
        let mut removed_count = 0;
        let removals_to_do = remove_keys.len().min(btree.len());

        for i in 0..removals_to_do {
            let len_before = btree.len();

            if let Some(entry) = unsafe { btree.first_entry_in(&alloc) } {
                let key = *entry.key();
                let (removed_key, removed_value) = entry.remove_entry();

                // Verify the removed entry
                assert_eq!(removed_key, key,
                    "Removal {}: key mismatch. insert_keys = {:?}, removed_keys = {:?}",
                    i, insert_keys, removed_keys);
                assert_eq!(removed_value, key * 2,
                    "Removal {}: value mismatch for key {}. insert_keys = {:?}, removed_keys = {:?}",
                    i, key, insert_keys, removed_keys);

                removed_keys.push(removed_key);
                removed_count += 1;

                // Verify tree length decreased by 1
                let len_after = btree.len();
                assert_eq!(len_after, len_before - 1,
                    "Removal {}: length didn't decrease correctly. Expected {}, got {}. Removed key: {}. insert_keys = {:?}, removed_keys = {:?}",
                    i, len_before - 1, len_after, removed_key, insert_keys, removed_keys);

                // Verify tree is still valid (in sorted order)
                let collected: Vec<_> = btree.iter().map(|(k, _)| *k).collect();
                let mut sorted = collected.clone();
                sorted.sort();
                assert_eq!(collected, sorted,
                    "Removal {}: tree not in sorted order after removing {}. insert_keys = {:?}, removed_keys = {:?}",
                    i, removed_key, insert_keys, removed_keys);
            }
        }

        assert_eq!(btree.len(), unique_inserts.len() - removed_count,
            "Final length mismatch. Expected {}, got {}. insert_keys = {:?}, removed_keys = {:?}",
            unique_inserts.len() - removed_count, btree.len(), insert_keys, removed_keys);

        core::mem::drop(btree);
        assert_eq!(alloc.net_allocations(), 0,
            "Memory leak detected! insert_keys = {:?}, removed_keys = {:?}",
            insert_keys, removed_keys);
    }
}

proptest! {
    #[test]
    fn test_removal_operations_old(
        insert_keys in prop::collection::vec(0..1000u32, 1..100),
        remove_keys in prop::collection::vec(0..1000u32, 0..50)
    ) {
        let alloc = CountingAllocator::default();
        let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

        // Insert all keys
        for k in &insert_keys {
            unsafe {
                btree.insert_in(&alloc, *k, k * 2)?;
            }
        }

        let unique_inserts: std::collections::HashSet<_> = insert_keys.iter().copied().collect();
        assert_eq!(btree.len(), unique_inserts.len());

        // Remove some keys using first_entry
        let mut removed_count = 0;
        for _ in 0..remove_keys.len().min(btree.len()) {
            if let Some(entry) = unsafe { btree.first_entry_in(&alloc) } {
                let _ = entry.remove_entry();
                removed_count += 1;
            }
        }

        assert_eq!(btree.len(), unique_inserts.len() - removed_count);

        core::mem::drop(btree);
        assert_eq!(alloc.net_allocations(), 0);
    }
}

proptest! {
    #[test]
    fn test_entry_api(
        keys in prop::collection::vec(0..1000u32, 1..100),
    ) {
        let alloc = CountingAllocator::default();
        let mut btree = AllocatedBTreeMap::<u32, u32, U1>::new_in(&alloc)?;

        // Use entry API to insert and modify
        for k in &keys {
            let entry = unsafe { btree.entry_in(&alloc, *k) };
            entry.insert(k * 2)?;
        }

        let unique_keys: std::collections::HashSet<_> = keys.iter().copied().collect();
        assert_eq!(btree.len(), unique_keys.len());

        // Use and_modify to increment existing values (only iterate over unique keys)
        for k in &unique_keys {
            let entry = unsafe { btree.entry_in(&alloc, *k) };
            let _ = entry.and_modify(|v| *v += 1);
        }

        // Verify modified values
        for k in unique_keys.iter() {
            assert_eq!(btree.get(k), Some(&(k * 2 + 1)));
        }

        core::mem::drop(btree);
        assert_eq!(alloc.net_allocations(), 0);
    }
}

proptest! {
    #[test]
    fn test_iterator_correctness(
        keys in prop::collection::vec(0..1000u32, 1..100),
    ) {
        let alloc = CountingAllocator::default();
        let btree: DropGuard::<AllocatedBTreeMap::<u32, u32, U1>, _> =
            keys.iter().map(|k| (*k, k * 2)).collect_in(&alloc)?;

        // Check that iterator yields elements in sorted order
        let collected: Vec<_> = btree.iter().map(|(k, _)| *k).collect();
        let mut sorted = collected.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(collected, sorted, "Iterator must yield elements in sorted order");

        // Check that iterator yields all unique elements
        let unique_keys: std::collections::HashSet<_> = keys.iter().copied().collect();
        assert_eq!(collected.len(), unique_keys.len());

        // Verify keys() iterator
        let keys_collected: Vec<_> = btree.keys().copied().collect();
        assert_eq!(keys_collected, sorted);

        // Verify values() iterator has matching length
        let values_count = btree.values().count();
        assert_eq!(values_count, unique_keys.len());

        core::mem::drop(btree);
        assert_eq!(alloc.net_allocations(), 0);
    }
}

#[test]
fn test_vacant_entry_key_below_key_above() -> Result<(), Box<dyn Error>> {
    let alloc = CountingAllocator::default();
    let mut btree = wrapper::NaiveBTreeMap::<_, _, U6, _>::new_in(&alloc)?;

    // Insert keys: 1, 3, 5, 7, 9
    btree.insert(5, "five")?;
    btree.insert(3, "three")?;
    btree.insert(7, "seven")?;
    btree.insert(1, "one")?;
    btree.insert(9, "nine")?;

    // Test key 4 (between 3 and 5)
    let entry = btree.entry(4);
    if let Entry::Vacant(v) = entry {
        assert_eq!(v.key_below(), Some(&3));
        assert_eq!(v.key_above(), Some(&5));
    } else {
        panic!("Expected vacant entry for key 4");
    }

    // Test key 0 (before minimum)
    let entry = btree.entry(0);
    if let Entry::Vacant(v) = entry {
        assert_eq!(v.key_below(), None);
        assert_eq!(v.key_above(), Some(&1));
    } else {
        panic!("Expected vacant entry for key 0");
    }

    // Test key 10 (after maximum)
    let entry = btree.entry(10);
    if let Entry::Vacant(v) = entry {
        assert_eq!(v.key_below(), Some(&9));
        assert_eq!(v.key_above(), None);
    } else {
        panic!("Expected vacant entry for key 10");
    }

    // Test key 2 (between 1 and 3)
    let entry = btree.entry(2);
    if let Entry::Vacant(v) = entry {
        assert_eq!(v.key_below(), Some(&1));
        assert_eq!(v.key_above(), Some(&3));
    } else {
        panic!("Expected vacant entry for key 2");
    }

    // Test key 8 (between 7 and 9)
    let entry = btree.entry(8);
    if let Entry::Vacant(v) = entry {
        assert_eq!(v.key_below(), Some(&7));
        assert_eq!(v.key_above(), Some(&9));
    } else {
        panic!("Expected vacant entry for key 8");
    }

    Ok(())
}

fn _assert_allocations<A: Allocator, B: ArrayLength>(alloc: CountingAllocator<A>, n_nodes: usize)
where
    U2: Mul<B>,
    Prod<U2, B>: ArrayLength,
    U1: Add<Prod<U2, B>>,
    Sum<U1, Prod<U2, B>>: ArrayLength,
{
    assert_eq!(alloc.net_allocations(), 0);
    assert_eq!(alloc.net_bytes_allocated(), 0);
    assert_eq!(alloc.n_allocations(), n_nodes);
    assert_eq!(alloc.n_deallocations(), n_nodes);
    assert_eq!(
        alloc.n_bytes_allocated(),
        n_nodes * size_of::<Node<u32, u32, B>>()
    );
    assert_eq!(
        alloc.n_bytes_deallocated(),
        n_nodes * size_of::<Node<u32, u32, B>>()
    );
}
