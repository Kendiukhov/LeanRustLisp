# FFI and ABI

## C ABI
LRL supports linking against C-compatible libraries.
- `extern "C"` functions are invoked via `unsafe` wrappers.
- Primitives must map to `LrlValue` (dynamic) or compatible Rust types (typed).

## Bindings
Bindings are currently manual. Future work includes `bindgen` integration.
