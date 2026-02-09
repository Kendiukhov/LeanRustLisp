# Ownership and Borrowing

LRL adopts Rust's ownership model to manage memory without a garbage collector.

## Ownership

Every value in LRL has a single owner. When you pass a non-`Copy` value to a function, you **move** it, transferring ownership.

```lisp
(inductive Resource (sort 1)
  (ctor acquire Resource))

(def use-resource (pi r Resource Nat)
  (lam r Resource zero))

(def create-and-use Nat
  (use-resource acquire))
```

### Copy Types

Simple types like `Nat` and `Bool` are `Copy`. They are duplicated when passed, so the original remains usable.

## Borrowing

You can allow temporary access to a value via **references**.

- `&T`: Shared (immutable) reference. Many allowed.
- `&mut T`: Mutable reference. Only one allowed (exclusive).

Borrow-centric examples often use `noncomputable` because references are lowered by the MIR phase.

### The Rules of Borrowing

1. At any given time, you can have either one mutable reference or any number of immutable references.
2. References must always be valid.

### Positive Example: Multiple Shared Borrows

```lisp
(noncomputable use-shared (pi r (Ref #[r] Shared Nat) Nat)
  (lam r (Ref #[r] Shared Nat) zero))

(noncomputable shared-borrows-ok (pi x Nat Nat)
  (lam x Nat
    (let r1 (Ref #[r] Shared Nat) (& x)
      (let r2 (Ref #[r] Shared Nat) (& x)
        (use-shared r1)))))
```

This is accepted: multiple shared borrows can coexist.

### Positive Example: Branch-Local Borrows

```lisp
(noncomputable use-mut (pi r (Ref #[r] Mut Nat) Nat)
  (lam r (Ref #[r] Mut Nat) zero))

(noncomputable branch-borrow-ok (pi x Nat (pi n Nat Nat))
  (lam x Nat
    (lam n Nat
      (match n Nat
        (case (zero)
          (let r (Ref #[r] Shared Nat) (& x)
            (use-shared r)))
        (case (succ k)
          (let m (Ref #[r] Mut Nat) (&mut x)
            (use-mut m)))))))
```

This is also accepted: borrows scoped inside separate match branches do not conflict.

### Rejected Example: Shared Then Mutable

```lisp
(noncomputable borrow-then-mutate (pi x Nat Nat)
  (lam x Nat
    (let r (Ref #[r] Shared Nat) (& x)
      (let m (Ref #[r] Mut Nat) (&mut x)
        (use-shared r)))))
```

`borrow-then-mutate` is rejected: mutable and shared borrows overlap on the same value.

This discipline prevents data races and iterator invalidation *at compile time*.
