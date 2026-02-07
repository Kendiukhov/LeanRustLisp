# Build Instructions

## Requirements
- Rust (latest stable).

## Commands

```bash
cargo build --release
cargo test
cargo run -p cli -- compile tests/file.lrl
```

## Environment Variables
- `LRL_DEFEQ_FUEL`: Control kernel fuel.
- `RUST_LOG`: Enable logging (if env_logger is configured).
