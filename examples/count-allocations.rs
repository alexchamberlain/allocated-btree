use rand::Rng;

use allocated::AllocErrorWithLayout;
use allocated::CountingAllocator;

use allocated_btree::btree::AllocatedBTreeMap as NaiveBTreeMap;
use allocated_btree::compressed::AllocatedBTreeMap as CompressedBTreeMap;

fn main() -> Result<(), AllocErrorWithLayout> {
    for i in 0..100 {
        // println!("RUN i={:?}", i);
        let compressed_alloc = CountingAllocator::default();
        let mut compressed_btree = CompressedBTreeMap::<u32, u32>::new_in(&compressed_alloc)?;

        let naive_alloc = CountingAllocator::default();
        let mut naive_btree = NaiveBTreeMap::<u32, u32>::new_in(&naive_alloc)?;

        let mut rng = rand::thread_rng();

        for _ in 0..1000 {
            let k: u32 = rng.gen();
            let v: u32 = rng.gen();

            unsafe {
                compressed_btree.insert_in(&compressed_alloc, k, v)?;
            }
            unsafe {
                naive_btree.insert_in(&naive_alloc, k, v)?;
            }

            println!(
                "{},compressed,{},{},{}",
                i,
                compressed_btree.len(),
                compressed_alloc.n_allocations(),
                compressed_alloc.n_bytes_allocated()
            );
            println!(
                "{},naive,{},{},{}",
                i,
                naive_btree.len(),
                naive_alloc.n_allocations(),
                naive_alloc.n_bytes_allocated()
            );
        }

        // unsafe { compressed_btree.drop_in(&compressed_alloc); }
        // unsafe { naive_btree.drop_in(&naive_alloc); }

        std::mem::drop(compressed_btree);
        std::mem::drop(naive_btree);

        assert_eq!(compressed_alloc.net_allocations(), 0);
        assert_eq!(naive_alloc.net_allocations(), 0);
    }

    // assert_eq!(btree.len(), 10);

    // println!("Naive node {}", std::mem::size_of::<Node<u32, u32, U6>>());
    // println!(
    //     "Compressed Interior node {}",
    //     std::mem::size_of::<InteriorNode<u32, u32, U6>>()
    // );
    // println!(
    //     "Compressed Leaf node {}",
    //     std::mem::size_of::<LeafNode<u32, u32, U6>>()
    // );

    // println!(
    //     "Compressed Allocations: {:?}",
    //     compressed_alloc.n_allocations()
    // );
    // println!(
    //     "Compressed Allocated Bytes: {:?}",
    //     compressed_alloc.n_bytes_allocated()
    // );

    // println!("Naive Allocations: {:?}", naive_alloc.n_allocations());
    // println!(
    //     "Naive Allocated Bytes: {:?}",
    //     naive_alloc.n_bytes_allocated()
    // );

    Ok(())
}
