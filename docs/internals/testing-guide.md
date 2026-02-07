# Testing Guide

## Test Suites
- `cargo test`: Unit tests for Rust components.
- `tests/*.lrl`: Integration tests compiled by the CLI.
  - `compile_test.lrl`: Basic compilation check.

## Adding Tests
1. Create a new `.lrl` file in `tests/`.
2. Add a `RUN` directive or similar harness (if applicable) or verify it compiles via `cargo run -p cli -- compile tests/new_test.lrl`.
