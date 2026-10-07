# Lean 4 comparison programs

Small, self-contained Lean 4 programs, one file per case. Each one shows one property from the
comparison (Q1 to Q12, as in `../results_rust_racket.md`) using only Lean core and `Std`, which ship
with the toolchain. The observed outcome of every file is recorded in `../results_lean_idris.md`.

A negative program (`*_neg.lean`) is its positive counterpart with the marked lines changed. Where
Lean 4 cannot reject the faulty program at all, the results table still lists it as a *negative*
whose expected outcome is `ACCEPT` or `RUNTIME_ERROR` (the violation is not detected, or detected
only at run time), as the Rust/Racket and LRL tables do; *limit* rows probe what Lean can express.

Run everything (Lean and Idris 2) and regenerate the results table:

```sh
CMP_BUILD_DIR=/some/tmp/dir case_studies/comparison/run_lean_idris.sh
```

Or check one file by hand (no build products are written):

```sh
cd case_studies/comparison/lean && lean Q6_wrong_state_neg.lean
```

The script type-checks each file with `lean FILE`. Accepted files that have a `main` are then built
into native executables with `lake build` (in a package under `$CMP_BUILD_DIR`, toolchain
`leanprover/lean4:v4.34.1`) and run. Files that contain `set_option trace.compiler.ir.result true`
print the compiler's final IR, which the results table quotes as evidence for Q1, Q4 and Q11.

| File | Q | Kind | What it shows |
|---|---|---|---|
| `Q1_head.lean` | Q1 | positive | A user-defined inductive family `Vec α n` with a one-case `Vec.head : Vec α (n + 1) → α`, and the core `Vector.head` (needs `NeZero n`). In the final IR, `Vec.head` is a field projection and `vectorHead` an array access whose bounds proof is an erased argument (`◾`); neither has a failure branch. |
| `Q1_head_empty_neg.lean` | Q1 | negative | `Vec.head` of `Vec.nil` is a type error. |
| `Q1_vector_head_empty_neg.lean` | Q1 | negative | `Vector.head` of an empty core `Vector`: no `NeZero 0` instance. |
| `Q2_append.lean` | Q2 | positive | `Vec.append : Vec α n → Vec α m → Vec α (m + n)` (index order chosen so that it type-checks by unfolding `Nat.add`), and the core `Vector.append` (`#check` prints its type). |
| `Q2_append_drop_neg.lean` | Q2 | negative | An `append` that drops an element does not have the sum type. |
| `Q3_reverse_involution.lean` | Q3 | positive | Proofs, by induction, that a user-defined list reverse and a user-defined length-preserving `Vec.reverse` (via `snoc`) are involutions; restates the core theorems `List.reverse_reverse` and `Vector.reverse_reverse`. `#print axioms` reports that `rev_rev` and `Vec.reverse_reverse` depend only on `propext`. |
| `Q3_reverse_wrong_neg.lean` | Q3 | negative | The false law `rev xs = xs` leaves an unsolved goal. |
| `Q4_erasure.lean` | Q4 | positive / limit | Final IR: a proof argument is marked erased (`◾`) and dropped by the specialised worker; a core `Vector` is passed as a bare `Array`; a subtype is a bare `Nat`. Limit: the `Nat` index of the user-defined family `Vec α n` is **not** erased: it is stored in every `cons` cell and passed to `Vec.push`, and `Vec.len` returns it at run time. Lean has no annotation that erases a data index. |
| `Q4_zero_divisor_neg.lean` | Q4 | negative | `safeDiv 10 0` with the proof `by decide`: rejected (`decide` proves that `0 > 0` is false). |
| `Q4_forge_neg.lean` | Q4 | negative | The proof argument of `safeDiv` is postulated with an `axiom` and used to divide by zero: accepted, runs (prints 0). Lean accepts axioms in ordinary code; a computable definition may use a propositional axiom. |
| `Q4_index_at_runtime_neg.lean` | Q4 | negative | The length index of the user-defined `Vec α n` returned as a run-time value (`Vec.len`): accepted (the index is not erased). |
| `Q5_channel.lean` | Q5, Q6 | positive | `Chan n`, a wrapper around `Std.CloseableChannel.Sync` indexed by the number of messages still to be sent: `send : Chan (n + 1) → Nat → IO (Chan n)`, `close : Chan 0 → IO Unit`. |
| `Q5_channel_reuse_neg.lean` | Q5 | negative | Reusing the channel after `send` is accepted (Lean has no linear or affine types); the second `close` fails at run time. |
| `Q6_wrong_state_neg.lean` | Q6 | negative | `close` on a `Chan 1` is a type error. |
| `Q7_send_vector.lean` | Q7 | positive | `sendAll : Vec Nat n → Chan n → IO (Chan 0)` ties the vector length to the protocol length. |
| `Q7_too_many_neg.lean`, `Q7_too_few_neg.lean` | Q7 | negative | Sending one message too many / too few is a type error. |
| `Q7_abandon_neg.lean` | Q7 | negative | A channel opened for 2 messages receives one and is dropped: accepted (no linear types), runs. |
| `Q8_macro.lean` | Q8 | positive | A command macro `protocol P carrying T` generates a typed channel type and typed operations; a term macro's template binder `x` does not capture the user's `x` (result 11, checked at compile time by `rfl`); a control macro that opts out of hygiene with `mkIdent` captures it (result 2). |
| `Q8_macro_ops_neg.lean` | Q8 | negative | Misusing a generated operation (closing with one message owed) is a type error. |
| `Q8_macro_global_names.lean` | Q8 | limit | A global name in a template refers to the definition-site constant (`Lib.helper`) even where another global or a local of the same name is in scope at the use site. |
| `Q9_two_refs.lean` | Q9 | positive | Two `IO.Ref`s to two locations passed to one function that writes through both. |
| `Q9_alias_neg.lean` | Q9 | negative | The same `IO.Ref` passed twice (two live mutable references to one location): accepted, both writes go to it. |
| `Q10_branch_consume.lean` | Q10 | positive | A channel consumed in both branches of an `if` is accepted (trivially: there is no usage check). |
| `Q10_use_after_neg.lean` | Q10 | negative | Using the channel after both branches consumed it is accepted; the extra `send` fails at run time. |
| `Q11_inplace.lean` | Q11 | positive | Pointer equality before/after `Vector.reverse` and `Array.set!`: the buffer is reused when the value is unshared and copied when it is shared. The final IR of a list reverse tests `isShared` and reuses the cons cell only when it is unshared. In-place update is a run-time decision (reference count 1), not a static guarantee. |
| `Q12_once_fn_neg.lean` | Q12 | negative | Lean 4 has no once-only (linear) function types: a closure that consumes a captured channel is called twice, compiles, and sends two messages on a channel typed for one. |

What Lean 4 does not provide here (observed in the results table):

- No usage discipline (linear, affine or once-only types). Reuse of a consumed value (Q5, Q10) and a
  second call of a once-only closure (Q12) are accepted. Where the library checks the protocol
  dynamically (`Std.CloseableChannel`), the error surfaces at run time.
- Data indices of inductive families are kept at run time (Q4). Proofs, types and the size proof
  of the core `Vector` are erased. A proof may be postulated with `axiom` in ordinary code (Q4).
- Mutable references (`IO.Ref`) may be aliased freely (Q9).
- In-place update (Q11) happens when the reference count is 1 at run time; sharing silently falls
  back to copying, and the type system does not say which case applies.

Q9 (two live mutable references to one location): Lean 4 has no borrowed references and no borrow
checker; its mutable references (`IO.Ref`) are ordinary values (`Q9_two_refs.lean`,
`Q9_alias_neg.lean`). The Idris 2 counterpart uses linear array handles (`../idris2/Q9_*.idr`).

Audit note (verification session, 2026-10-05): `Q4_zero_divisor_neg.lean`, `Q4_forge_neg.lean`,
`Q4_index_at_runtime_neg.lean`, `Q7_abandon_neg.lean`, `Q9_two_refs.lean` and `Q9_alias_neg.lean`
were added so that Lean faces the same violations as the LRL and Rust programs, and
`Q5_channel_reuse_neg.lean`, `Q10_use_after_neg.lean`, `Q12_once_fn_neg.lean` are now listed as
negatives (they were *limit* rows). `CMP_BUILD_DIR=<tmp> case_studies/comparison/run_lean_idris.sh`
then reported 71 of 71 cases as expected; every outcome stated above for these files is a row of
`../results_lean_idris.md`.
