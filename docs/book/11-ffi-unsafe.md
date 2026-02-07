# FFI and Unsafe

Just like Rust, LRL has an `unsafe` keyword that allows you to bypass certain checks.

## Unsafe

`unsafe` blocks allow you to:
- Call `extern` functions (FFI).
- Dereference raw pointers.
- Implement `unsafe` traits.

```lisp
(unsafe
  (call-external-function args))
```

## Foreign Function Interface (FFI)

LRL can link against C ABI libraries.

```lisp
(extern "C" {
  (def put-char (-> Int Int))
})
```

## Safe Wrappers

The idiomatic way to handle unsafe code is to wrap it in a safe interface that enforces the invariants that the compiler can't check.

```lisp
(def print-secure (-> String Unit)
  (lam s String
    (unsafe
       ;; ... low level implementation ...
       unit)))
```
