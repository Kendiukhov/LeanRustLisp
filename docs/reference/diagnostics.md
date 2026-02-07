# Diagnostics

## Error Codes

### Kernel (Kxxxx)
Errors dealing with the core logic and type system.
- `K0001`: Unknown variable.
- `K0002`: Type mismatch.
- `K0005`: Unknown inductive.
- `K0015`: Non-positive inductive occurrence.
- `K0018`: Non-terminating recursion.
- `K0021`: Ownership violation.

### Frontend (Fxxxx)
Errors in parsing or elaboration.
- `F0001`: Unexpected EOF.
- `F0200`: Unbound variable.
- `F0202`: Ambiguous constructor.
- `F0211`: Non-exhaustive match.

## Flags

- `--trace-macros`: Print macro expansion steps.
- `--trace-elaboration`: Print elaboration trace.
- `-D <code/category>`: Deny warning.
- `-A <code/category>`: Allow warning.
