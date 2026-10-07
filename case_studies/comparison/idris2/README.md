# Idris 2 comparison programs

Small, self-contained Idris 2 programs, one file per case. Each one shows one property from the
comparison (Q1 to Q12, as in `../results_rust_racket.md`) using the libraries that ship with
Idris 2 0.8.0: `base` (`Data.Vect`, `Data.List`, `Language.Reflection`), `linear`
(`Control.Linear.LIO`, `System.Concurrency.Session`, `Data.Linear.LVect`) and `contrib`
(`Data.Linear.Array`). The observed outcome of every file is recorded in `../results_lean_idris.md`.

A negative program (`*_neg.idr`) is its positive counterpart with the marked lines changed.

Run everything (Lean and Idris 2) and regenerate the results table:

```sh
CMP_BUILD_DIR=/some/tmp/dir case_studies/comparison/run_lean_idris.sh
```

Or check one file by hand, keeping build products out of the repository:

```sh
cd case_studies/comparison/idris2
idris2 -p linear -p contrib --build-dir /tmp/idris-build --check Q5_channel_reuse_neg.idr
```

Files with a `main` are compiled by the script with
`idris2 -p linear -p contrib --dumpcases CASES -o NAME FILE` (Chez Scheme back end) and run; the
compiled case trees written by `--dumpcases` are the evidence for Q1, Q4 and Q11. Files without
`main` are checked with `--check`.

| File | Q | Kind | What it shows |
|---|---|---|---|
| `Q1_head.idr` | Q1 | positive | A user-defined `Vec` with a one-clause `total vhead : Vec (S n) a -> a`, and the library's `Data.Vect.head`. Both compiled case trees have a single branch and no default branch. |
| `Q1_head_empty_neg.idr` | Q1 | negative | `Data.Vect.head` of an empty `Vect` is a type error. |
| `Q2_append.idr` | Q2 | positive | `append : Vec n a -> Vec m a -> Vec (n + m) a`, and the library's `(++)` on `Vect`. |
| `Q2_append_drop_neg.idr` | Q2 | negative | An `append` that drops an element does not have the sum type. |
| `Q3_reverse_involution.idr` | Q3 | positive | Total proofs that a user-defined list reverse and a length-preserving `vrev : Vect n a -> Vect n a` (via `Data.Vect.snoc`) are involutions; restates the library's `Data.List.reverseInvolutive`. |
| `Q3_reverse_wrong_neg.idr` | Q3 | negative | The false law `rev xs = xs` is rejected. |
| `Q4_erasure.idr` | Q4 | positive | Compiled case trees: a quantity-0 proof argument is absent from the definition and from its call site; the unbound implicit length index of `Vec` is absent from `cons` cells and from `push`; an index bound with unrestricted quantity (`{n : Nat}`) is passed at run time. |
| `Q4_erased_index_neg.idr` | Q4 | negative | Using a quantity-0 index at run time is rejected. |
| `Q4_zero_divisor_neg.idr` | Q4 | negative | `safeDiv 10 0` with the proof `ItIsSucc` (a proof of `NonZero (S n)`): type error. |
| `Q4_forge_neg.idr` | Q4 | negative | The quantity-0 proof argument of `safeDiv` is forged with `believe_me` and used to divide by zero: accepted by the type checker; at run time `Data.Nat.divNat` has no case for 0 and the program stops with an error. |
| `Q5_channel.idr` | Q5, Q6 | positive | A session-typed linear channel from `System.Concurrency.Session` (`send` takes the channel with quantity 1 and returns it at the next protocol state), run between two threads with `fork`. |
| `Q5_channel_reuse_neg.idr` | Q5 | negative | Using the channel again after `send` is rejected (two uses of a linear name). |
| `Q6_wrong_state_neg.idr` | Q6 | negative | `end` on a channel that still owes a message is a type error. |
| `Q7_send_vector.idr` | Q7 | positive | `Msgs n` is the session "send n numbers, then end"; `sendAll : Vect n Nat -> Channel (Msgs n) -@ L IO ()` sends every element and ends the channel. |
| `Q7_too_many_neg.idr`, `Q7_too_few_neg.idr` | Q7 | negative | Sending one message too many / too few is a type error. |
| `Q7_abandon_neg.idr` | Q7 | negative | A sender for a 2-message protocol sends one message and leaves the channel unused: rejected (0 uses of a linear name). |
| `Q8_macro.idr` | Q8 | positive | Elaborator reflection: an elaborator script declares a typed channel type and typed operations, run with `%runElab`. A `%macro` whose quoted template binds `x` captures the user's `x` (result 2): Idris 2 quotes are not hygienic. The same macro written with `genSym` does not capture (result 11). |
| `Q8_macro_ops_neg.idr` | Q8 | negative | Misusing a generated operation (closing with one message owed) is a type error. |
| `Q8_macro_global_names.idr` | Q8 | limit | A free global name in a quoted template is resolved at the use site: a local `let helper` captures it. Writing the qualified name `Lib.helper` pins it to the definition site. |
| `Q8_macro_global_ambiguous.idr` | Q8 | limit | The same macro used in a namespace that defines its own global `helper`: elaboration reports an ambiguity. |
| `Q9_two_arrays.idr` | Q9 | positive | No borrowed references: the closest counterpart is a linear handle to a mutable array (`Data.Linear.Array`); `touch2` writes through two handles of two different arrays. |
| `Q9_alias_neg.idr` | Q9 | negative | The same linear array handle passed twice: rejected (2 uses of a linear name). Unrestricted `IORef`s, by contrast, may be aliased (not tested). |
| `Q10_branch_consume.idr` | Q10 | positive | A linear channel consumed in both branches of an `if` is accepted. |
| `Q10_use_after_neg.idr` | Q10 | negative | Using the channel after a call that consumed it in both branches is rejected. |
| `Q10_branch_drop_neg.idr` | Q10 | limit | Quantity 1 means *exactly* once: a channel used in one branch and not in the other is rejected ("Inconsistent usage"). An affine discipline would accept it. |
| `Q11_inplace.idr` | Q11 | positive / limit | `Data.Linear.Array`: a linear handle to a mutable array; `write` returns the same array after `Data.IOArray.writeArray`, whose generated Chez Scheme uses `vector-set!`; an array is reversed by swaps. Limit: `Data.Linear.LVect.reverse` (a consuming reverse of a linear length-indexed vector) builds a new cons cell per element in its compiled case tree. |
| `Q11_array_reuse_neg.idr` | Q11 | negative | Reading the old array handle after `write` consumed it is rejected. |
| `Q12_once_fn.idr` | Q12 | positive | A function parameter of quantity 1 (`(1 k : ...)`) is called once; the closure passed for it captures a linear channel. |
| `Q12_once_fn_neg.idr` | Q12 | negative | Calling the quantity-1 function twice is rejected. |
| `Q12_capture_unrestricted_neg.idr` | Q12 | negative | Passing a closure that captures a linear channel where an unrestricted function is expected is rejected. |

What differs from an affine ownership discipline (observed in the results table):

- Quantity 1 is linear, not affine: every linear value must be used exactly once on every path
  (Q10_branch_drop_neg), so a protocol cannot be abandoned silently, but a value also cannot simply
  be dropped.
- Elaborator-reflection quotes are not hygienic (Q8): binders in a template and free names in it
  are resolved where the macro is used. Hygiene is obtained by hand (`genSym`, qualified names).
- Indices are erased only when their quantity is 0; an index that the program needs at run time
  must be bound with unrestricted quantity and is then passed as an ordinary argument (Q4).

Q9 (two live mutable references to one location): Idris 2 has no borrowed references and no borrow
checker; the Q9 programs use linear array handles, whose aliasing the linearity check rejects. The
Lean 4 counterpart uses `IO.Ref` (`../lean/Q9_*.lean`).

Audit note (verification session, 2026-10-05): `Q4_zero_divisor_neg.idr`, `Q4_forge_neg.idr`,
`Q7_abandon_neg.idr`, `Q9_two_arrays.idr` and `Q9_alias_neg.idr` were added so that Idris 2 faces
the same violations as the LRL and Rust programs. `CMP_BUILD_DIR=<tmp>
case_studies/comparison/run_lean_idris.sh` then reported 71 of 71 cases as expected; every outcome
stated above for these files is a row of `../results_lean_idris.md`. The `LinArray` API used by
`Q9_*.idr` (`write`, `read`, `toIArray`, `newArray`) was read in
`contrib-0.8.0/Data/Linear/Array.idr` under `idris2 --libdir`.
