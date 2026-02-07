# Codegen Guide

## Overview
The `codegen` crate translates MIR to Rust.

## Pipeline
1. **Lowering**: MIR types/statements -> Rust AST.
2. **Runtime Support**: Linking against `lrl_rt` (runtime library) which provides `Nat`, closures, etc.
3. **Output**: Generates a `.rs` file which is then compiled by `rustc`.

## Erasure
Ensure `Prop` elements are erased to `()` or dropped entirely.
