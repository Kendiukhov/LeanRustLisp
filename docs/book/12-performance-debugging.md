# Performance and Debugging

## Performance Model

LRL compiles to native code via Rust.

- **Erasure**: Everything in `Prop` is erased.
- **Monomorphization**: Generic functions are typically monomorphized (like Rust), leading to efficient code but larger binaries.
- **Reference Counting**: Currently, some structures may use RC, but the goal is affine types minimizing this overhead.

## Positive Property Examples

### Proof-Carrying API Without Runtime Proof Cost

```lisp
(def with-self-eq
  (pi n Nat (pi p (Eq Nat n n) Nat))
  (lam n Nat
    (lam p (Eq Nat n n)
      (add n n))))

(def entry Nat
  (with-self-eq (succ (succ zero))
                (refl Nat (succ (succ zero)))))
```

`p` is checked by the type checker but erased at runtime.

### Predictable Structural Cost

```lisp
(def sum-list (pi xs (List Nat) Nat)
  (lam xs (List Nat)
    (match xs Nat
      (case (nil) zero)
      (case (cons h t ih) (add h ih)))))
```

`sum-list` does one recursive step per element. No hidden tracing GC pauses are introduced by this definition pattern.

## Debugging

### Inspecting Generated Code

If you compile with:
```bash
cargo run -p cli -- compile file.lrl -o out --backend typed
```
The compiler currently generates an intermediate Rust file `output.rs` in `build/`. You can inspect this to see exactly what LRL is producing.

Useful companions while debugging:

```bash
cargo run -p cli -- compile-mir file.lrl
cargo run -p cli -- --expand-full file.lrl
```

- `compile-mir` helps verify borrow/lifetime lowering.
- `--expand-full` lets you inspect macro output before type checking.

### Profiling
(Future) Integration with standard profilers like `perf` or `Instruments` is planned.
