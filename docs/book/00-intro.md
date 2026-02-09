# Introduction

LeanRustLisp (LRL) is an experimental programming language designed to unify three powerful concepts:

1.  **Lean-grade Specification**: Using dependent types and inductive families to specify precise program behavior and prove correctness.
2.  **Rust-grade Resource Discipline**: Using affine types, ownership, and borrow checking to manage memory and resources safely and efficiently without garbage collection.
3.  **Lisp-grade Extensibility**: Using S-expressions and hygienic macros to allow the language to be extended and programmed by the user.

## The Three Pillars

### Systems Performance
LRL aims to be a systems language. By adopting Rust's ownership model, it avoids the runtime overhead of a garbage collector, making it suitable for real-time and resource-constrained environments.

### Correctness
With a core calculus based on the Calculus of Inductive Constructions (CIC), LRL allows you to express complex invariants in your types. You can write proofs that your code satisfies these invariants, and the compiler checks them.

### Extensibility
The "Lisp" in the name isn't just about parentheses. It's about the philosophy that the language should be programmable. Macros allow you to define new syntactic forms that desugar into core concepts, making the language adaptable to your domain.

## Three Small Examples

```lisp
;; 1) Correctness: proof checked by type checker.
(def zero-is-zero (Eq Nat zero zero)
  (refl Nat zero))

;; 2) Resource discipline: borrowing is explicit.
(noncomputable shared-borrow (pi x Nat Nat)
  (lam x Nat
    (let r (Ref #[r] Shared Nat) (& x)
      x)))

;; 3) Extensibility: syntax transformation via macro.
(defmacro mk-inc (v)
  (quasiquote (add (unquote v) (succ zero))))

(def demo Nat (mk-inc (succ zero)))
```

These examples illustrate a recurring theme in LRL: strong static guarantees with straightforward runtime behavior.

## What LRL is NOT

- **A Dynamic Scripting Language**: While it looks like Lisp, it is statically typed and compiled.
- **A General Proof Assistant**: While it has proof capabilities, the focus is on verifying software, not general mathematics (though it shares the same foundations as Lean/Coq).
- **Finished**: LRL is currently in Alpha.
