# Function and Closure Kinds

This document specifies function/closure kinds, capture rules, and ownership
semantics. It is the source of truth for downstream implementation streams.

## Goals

- Prevent unsound duplication of closures that capture linear values.
- Match Rust-style calling semantics (shared vs mutable vs consuming calls).
- Provide explicit syntax and a stable core representation.

## 1. Kinds

LRL defines three function kinds:

- **Fn**: callable with a shared borrow of its environment.
- **FnMut**: callable with a mutable borrow of its environment.
- **FnOnce**: callable by consuming its environment.

These are ordered by capability:

```
Fn < FnMut < FnOnce
```

A value of a smaller kind can be used where a larger kind is expected
(coercion rules below).

## 2. Surface Syntax

Function kinds are optional annotations on `lam` and `pi`.
If omitted, the default is `fn`. In v0, inference-only is acceptable; the
annotation form is reserved for future control and clearer errors.

**Preferred (attribute) form:**

```
(lam #[once] x A body)
(lam #[fn] x A body)
(lam #[mut] x A body)

(pi #[once] x A B)
(pi #[fn] x A B)
(pi #[mut] x A B)
```

**Legacy sugar (accepted during migration):**

```
(lam x A body)                 ; default fn
(lam fn x A body)
(lam fnmut x A body)
(lam fnonce x A body)

(pi x A B)                      ; default fn
(pi fn x A B)
(pi fnmut x A B)
(pi fnonce x A B)
```

Implicit binders keep the same brace syntax:

```
(lam fn {x} A body)
(pi fnonce {x} A B)
(lam #[once] {x} A body)
(lam #[mut] {x} A body)
(pi #[once] {x} A B)
(pi #[mut] {x} A B)
```

Legacy sugar is desugared to the attribute form during elaboration.

### 2.1 Lifetime Labels for References

Function *types* may label reference lifetimes by attaching an attribute to
`Ref` in the signature. The label becomes a named region parameter; reusing the
same label ties lifetimes together.

Example (return tied to the first argument):

```
(pi a (Ref #[a] Shared Nat)
  (pi b (Ref #[b] Shared Nat)
    (Ref #[a] Shared Nat)))
```

Elision rule (Rust‑style): if a signature contains exactly one distinct
reference lifetime among its inputs, unlabeled return references are assigned
that lifetime. Otherwise, return references must be explicitly labeled.
A *signature* is a complete chain of `pi`s (all the arguments of a curried
function type, up to its final result); the rule is checked once per chain, not
for each curried suffix. Each unlabeled input reference counts as a lifetime of
its own. So `(pi a (Ref Shared Nat) (pi n Nat (Ref Shared Nat)))` (one input
lifetime, the reference first) is accepted like `(pi n Nat (pi a (Ref Shared Nat)
(Ref Shared Nat)))`, while two unlabeled input references, or none, with an
unlabeled result are rejected (`F0208` in the elaborator, `K0045` in the kernel).
A `pi` appearing as an argument type or inside the result is a signature of its own.

**Elision as sugar:** An elided label is treated as a fresh implicit label
variable during elaboration. If an expected type provides an explicit label,
the elided label may unify to that explicit label; explicit-to-explicit
mismatches remain errors. After elaboration, labels are concrete and compared
strictly by defeq.

## 3. Core Representation

Extend core terms with a function kind annotation:

```
FnKind ::= Fn | FnMut | FnOnce

Lam(ty, body, binder_info, fn_kind)
Pi(ty, body, binder_info, fn_kind)
```

`fn_kind` is part of the type identity. `Pi^Fn` is **not** definitionally equal
to `Pi^FnOnce`; coercions must be explicit or inserted by elaboration.

## 4. Capture Inference

The kind describes how a closure uses its **captured environment** (the
variables bound outside the lambda), not how it uses its own argument: a
lambda that consumes its own parameter can still be `Fn`.

The required kind of `λx. body` is computed from the *uses* of the variables
free in `body` (`kernel::checker::term_variable_uses`, rules in
`docs/spec/ownership_model.md` §6.2). Each use is a read, a mutable use or a
move:

- occurrences in **erased positions** — types, proofs, motives, recursor
  parameters and indices, type arguments, proof arguments — are reads (they
  never raise the kind);
- calling an `Fn` / `FnMut` / `FnOnce` function variable is a read / mutable
  use / move of it;
- `borrow_shared x` (`& x`) reads `x`; `borrow_mut x` (`&mut x`) uses `x`
  mutably;
- any other runtime occurrence (argument, constructor field, result) is a move;
- inside a nested lambda of kind `k`, a use counts as at most `k`'s capture
  mode (`Fn`: read, `FnMut`: mutable use, `FnOnce`: move).

Each captured variable is then classified by capture mode:

- **By copy / shared borrow** (read): its type is Copy, or it is only read.
- **By mutable borrow**: it is not Copy and is used mutably (or it is a
  `Ref Mut` value that is passed on, i.e. reborrowed).
- **By move**: it is not Copy and is moved.

Kind inference rule (take the maximum over captures):

- Any **move** capture => `FnOnce`
- Else any **mutable borrow** capture => `FnMut`
- Else => `Fn`

An explicit annotation must be **at least** the inferred kind
(annotating with a more permissive kind is allowed; annotating with a smaller
kind is an error: `F0207` for a lambda's own annotation, `F0206` when the
lambda is checked against a `pi` of a smaller kind).

The elaborator, the kernel re-check (`K0043`) and MIR lowering (required
capture modes) all use this one analysis, so they agree on every kind. (The
elaborator falls back to a syntactic approximation only for a body the kernel
cannot type yet, e.g. one with unsolved metavariables.)

### 4.1 Implicit binders are observational-only

Implicit binders (`{x}`) are inference markers, not a license to consume
resources. In v0, implicit **value** binders are restricted to
observational usage:

- They may appear freely in types and in `Prop` (erased usage).
- At runtime they may only be read or copied; they must not be moved,
  mutably borrowed, or stored in non-Copy positions.
- Passing an implicit argument to a parameter that consumes or mutably
  borrows it is an error.

If a value needs to be consumed, make the binder explicit. This rule lets
kind inference treat implicit arguments as non-consuming; any consuming use
is rejected rather than silently upgrading the closure kind.

## 5. Coercions and Subtyping

Coercions follow the kind ordering:

- `Fn` can be used as `FnMut`.
- `FnMut` can be used as `FnOnce`.
- (`Fn` can be used as `FnOnce` via the above.)

No coercion exists in the other direction. The elaborator may insert eta-wrappers
or coercion nodes to account for expected kinds.

## 6. Call Semantics and Ownership

Function application borrows or consumes the function value based on its kind:

- **Fn** call: shared-borrow the closure environment.
- **FnMut** call: mutable-borrow the closure environment.
- **FnOnce** call: move the closure environment (consumes it).

This ensures:

- `Fn` values can be called multiple times without requiring `Copy`.
- `FnOnce` values can be called at most once.

Borrow checking enforces the required aliasing rules for `Fn` calls.

Lowering to MIR should preserve call mode explicitly (e.g., `CallShared` for
`Fn`, `CallConsume` for `FnOnce`).

## 7. Copy Rules for Function Values (Current Policy)

Function *types* (`Pi`) are **not** `Copy`. Function **items** (top-level
non‑capturing definitions) are `Copy` by default. **Closures** are non‑Copy
by default, even when their kind is `Fn`/`FnMut` and all captures are `Copy`.
Repeated calls are still allowed because `Fn` calls borrow the environment,
while `FnOnce` calls consume it.

If you need to duplicate a closure value today, pass it by shared reference
or lift it to a top-level definition (no captured environment). A future
extension may allow capture‑aware Copy for closures.

## 8. Dependent Types and Erasure

`FnKind` is tracked uniformly in `Pi` even when the binder is implicit or the
function lives in `Prop`. The kind does not affect beta-reduction or erasure;
it only affects ownership/borrow semantics for runtime values.

## 9. Examples (for Tests)

These examples are intended to seed regression tests. They illustrate kind
inference, explicit annotations, and coercions. The syntax here matches the
surface syntax in this spec.

When `#[once]`/`#[fn]` (or legacy `pi fn`/`pi fnonce`) appears, it is an explicit
annotation; removing it should still infer the same kind.

### 9.1 Inferred `Fn` (read-only capture)

```lisp
(def make_adder
  (pi x Nat (pi fn y Nat Nat))
  (lam x Nat
    ;; `x` is read-only => inferred Fn.
    (lam y Nat (add x y))))
```

### 9.2 Inferred `FnOnce` (move capture)

The captured value must be non-Copy for the capture to be a move. (A type
whose fields are all Copy, such as `Box Nat` with
`(inductive Box (pi A (sort 1) (sort 1)) (ctor mk_box (pi {A (sort 1)} (pi x A (Box A)))))`,
derives Copy, so capturing it is a copy and the closure is `Fn`.) The
`affine` marker makes a type non-Copy:

```lisp
(inductive (affine) Ticket (sort 1)
  (ctor mk_ticket (pi id Nat Ticket)))

(def make_once
  (pi t Ticket (pi #[once] _ Nat Ticket))
  (lam t Ticket
    ;; Captures the affine `t` by move => inferred FnOnce (even if not annotated).
    (lam _ Nat t)))
```

### 9.3 Inferred `FnMut` (mutable capture)

```lisp
(def step_twice
  (pi g (pi #[mut] x Nat Nat) (pi #[mut] n Nat Nat))
  (lam g (pi #[mut] x Nat Nat)
    ;; Calls the captured FnMut function `g` (a mutable use of `g`) => inferred FnMut.
    (lam #[mut] n Nat (g (g n)))))

(def step_twice_bad
  (pi g (pi #[mut] x Nat Nat) (pi n Nat Nat))
  (lam g (pi #[mut] x Nat Nat)
    ;; ERROR (F0206): requires FnMut, the expected type says Fn.
    (lam n Nat (g (g n)))))
```

### 9.4 Explicit Kind Too Small (error)

```lisp
(inductive (affine) Ticket (sort 1)
  (ctor mk_ticket (pi id Nat Ticket)))

(def bad_kind
  (pi t Ticket (pi #[fn] _ Nat Ticket))
  (lam t Ticket
    ;; ERROR (F0207): inferred FnOnce, annotated as Fn.
    (lam #[fn] _ Nat t)))
```

### 9.5 Coercion: `Fn` to `FnOnce`

```lisp
(def apply_once
  (pi f (pi #[once] x Nat Nat) (pi #[once] v Nat Nat))
  (lam f (pi #[once] x Nat Nat)
    ;; The inner closure captures `f` and calls it; an FnOnce call consumes `f`,
    ;; so the inner closure is itself FnOnce (with `(pi v Nat Nat)` here the
    ;; definition is rejected: F0206, expected Fn, got FnOnce).
    (lam #[once] v Nat (f v))))

(def add_one
  (pi #[fn] x Nat Nat)
  (lam x Nat (succ x)))

;; Coerces `add_one : Fn` into `FnOnce` at the call.
(def test_coercion Nat (apply_once add_one zero))
```

The programs of §9.1–§9.5 are checked by `cli/tests/ownership_soundness.rs`
(`function_kinds_spec_examples`).
