# Use Cases

Why LeanRustLisp? Here are the problems we solve.

---

## Verified Systems Programming

**Problem**: C/C++ are unsafe. Rust is safe but hard to verify formally.

**Solution**: LRL allows you to write low-level code with integrated proofs of correctness.

**Status**: _Planned_

---

## Safe High-Performance Infrastructure

**Problem**: High-performance code often requires `unsafe` in Rust.

**Solution**: Dependent types can express invariants (like buffer sizes or state machine transitions) that remove the need for runtime checks without `unsafe`.

**Status**: _Early Access_

---

## DSLs and Tooling

**Problem**: Creating a new language is hard.

**Solution**: LRL's Racket-like macro system makes it a "language for building languages."

**Status**: _Available_

---

## Security-Sensitive Capability Code

**Problem**: Access control is often implicit.

**Solution**: Linear capability tokens (`IO`, `Network`) enforce security policies at the type level.

**Status**: _Designing_

---

## Proof-Carrying APIs

**Problem**: APIs rely on documentation for constraints ("must call init first").

**Solution**: Types encode the protocol. A function strictly cannot be called in the wrong state.

**Status**: _Available_

---

## Research & Education

**Problem**: PL research languages are often slow or garbage collected.

**Solution**: LRL provides a playground for type theory that compiles to standard, fast systems code.

**Status**: _Available_
