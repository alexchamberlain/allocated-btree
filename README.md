# allocated-btree

[![crates.io](https://img.shields.io/crates/v/allocated-btree.svg)](https://crates.io/crates/allocated-btree)
[![Released API docs](https://docs.rs/allocated-btree/badge.svg)](https://docs.rs/allocated-btree)

An implementation of a B-Tree using the allocated pattern.

This crate provides 2 main interfaces:
* `allocated_btree::AllocatedNaiveBTreeMap` - a naive BTree that uses a single node shape
* `allocated_btree::AllocatedCompressedBTreeMap` - a compressed BTree that uses an optimised leaf node

The compressed data structure uses around 50% of the memory of the naive data structure.

Most of this code was written before code generating AI was
widespread. However, Claude Code has been used to fix a couple of bugs, fix typos and improve
the documentation since then.

## Motivation

The main motivation for this crate is to serve as an example of how to use the `allocated` crate, especially how to compare 2 data structures using an allocator.

## License

Copyright 2024 Alex Chamberlain

This project is licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or
  http://opensource.org/licenses/MIT)

at your option.
