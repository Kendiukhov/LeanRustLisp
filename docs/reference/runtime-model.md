# Runtime Model

## Data Representation

- **Nat**: Arbitrary precision integers (BigInt).
- **Inductives**: Tagged unions or struct pointers.
- **Closures**: `(Result, Environment)` pairs.

## Erasure

The compiler performs full erasure of:
- `Prop` types and values.
- Type parameters (polymorphism is monomorphized or erased depending on backend).
- `PhantomData`.

## Memory Management

LRL uses Affine Types to minimize GC.
- Unique data is managed manually (drop flags).
- Shared data may use Reference Counting (Ref/Shared).
