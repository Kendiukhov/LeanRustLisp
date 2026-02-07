# Foreign Function Interface

Interfacing with other languages.

## Extern Blocks

Primitive constants can be declared without value.

```lisp
(def my-c-func (-> Int Int))
```

To actually link, these must be mapped to native symbols in the backend.

## Unsafe

Calling foreign functions is generally `unsafe` because the FFI cannot guarantee LRL's invariants (validity, total functions, etc).

`unsafe` blocks allow:
- Calling external primitives.
- Bypassing some memory safety checks.
