# Concurrency

LRL provides primitives for safe concurrency, relying on the type system to prevent data races.

## Primitives

Concurrency support is provided by runtime primitives marked with specific attributes:
- `concurrency_primitive`: Mutexes, Channels.
- `atomic_primitive`: Atomic integers/booleans.

## Safety

The type system (and future `Send`/`Sync` traits) ensures that mutable data cannot be shared across threads without synchronization (Mutex).
- **Interior Mutability**: Types like `RefCell` or `Mutex` allow mutation through shared references (`&T`).
- **Markers**: The kernel tracks interior mutability via the `interior_mutable` marker to ensure `Copy` safety (types with interior mutability cannot be trivially `Copy` unless safe).
