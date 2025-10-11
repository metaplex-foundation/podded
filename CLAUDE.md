# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

### Build and Check
- `cargo build` - Build the library
- `cargo check` - Quick compilation check without producing artifacts
- `cargo clippy` - Run Rust linter (currently has warnings about ambiguous glob re-exports in src/pod/mod.rs that need fixing)

### Testing
- `cargo test` - Run all tests
- `cargo test <test_name>` - Run specific test by name
- `cargo test --lib` - Run only library tests

## Architecture

Podded is a Rust library providing zero-copy types optimized for constraint environments like Solana programs. The library is organized into three main modules:

### Core Structure
- **`src/lib.rs`**: Defines the `ZeroCopy` trait for zero-copy deserialization using bytemuck
- **`src/pod/`**: Pod-enabled primitive types (booleans, strings, options, unsigned integers, optional pubkeys)
- **`src/collections/`**: Zero-copy collections (AVL trees, hash sets) with immutable and mutable variants
- **`src/types/`**: Additional utility types (prefix strings)

### Key Design Patterns
- All types implement or work with `bytemuck::Pod` for zero-copy operations
- Collections provide both immutable (`AVLTree`, `HashSet`) and mutable (`AVLTreeMut`, `HashSetMut`) interfaces
- Types are designed for use in Solana programs where memory layout and zero-copy performance are critical

### Current Issues
- Ambiguous glob re-exports warning in `src/pod/mod.rs:8-11` where `PodBool` is re-exported from multiple modules
- Unused import warnings for `pod_bool::*` and `pod_unsigned::*` in the same file

## Dependencies
- `bytemuck ^1.14` - Core dependency for Pod trait and zero-copy operations
- `solana-program <3` - Solana program compatibility