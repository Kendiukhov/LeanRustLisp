# Performance and Debugging

## Performance Model

LRL compiles to native code via Rust.

- **Erasure**: Everything in `Prop` is erased.
- **Monomorphization**: Generic functions are typically monomorphized (like Rust), leading to efficient code but larger binaries.
- **Reference Counting**: Currently, some structures may use RC, but the goal is affine types minimizing this overhead.

## Debugging

### Inspecting Generated Code

If you compile with:
```bash
cargo run -p cli -- compile file.lrl -o out --backend typed
```
The compiler currently generates an intermediate Rust file `output.rs` in `build/`. You can inspect this to see exactly what LRL is producing.

### Profiling
(Future) Integration with standard profilers like `perf` or `Instruments` is planned.
