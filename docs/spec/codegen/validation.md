# Validation

## Output Validation
Generated Rust code is compiled by `rustc`.
- Borrow checker errors in generated code indicate bugs in LRL's MIR borrow checker.
- Valid LRL programs should produce valid Rust code (no panics, no UB).
