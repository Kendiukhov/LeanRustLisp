# LRL case studies

Complete, runnable LRL programs for the evaluation of the paper, with negative variants
(`neg/`) that must be rejected. Run every command from the repository root: the CLI finds
`stdlib/` relative to the current directory. `lrl` below is the CLI binary
(`cargo build -p cli` produces it as `target/debug/cli`, or under `$CARGO_TARGET_DIR`).

## A. Length-indexed vectors with kernel-checked proofs (`vectors.lrl`)

### What the program shows

`vectors.lrl` is a complete program (every body is written out): length-indexed vectors, total
operations whose types carry the length, and proofs about `vreverse` that the kernel checks like
any other definition. Implicit arguments (`{A}`, `{n}`) are inferred everywhere.

* **The type.** `Vec A n` has the element type `A` as a parameter and the length `n` as an index:
  `vnil : Vec A zero`, `vcons : {n} -> A -> Vec A n -> Vec A (succ n)`. `Unit` is declared in the
  file (the prelude has no `Unit`, `Vec` or `Fin`).
* **A total head without a run-time check.** `vhead : {A} {n} -> Vec A (succ n) -> A` is a
  dependent match whose motive computes the result type from the length: `Unit` at `zero`, `A` at
  a successor. The `vnil` case is checked against `Unit` and returns `unit`; for the argument's
  type `Vec A (succ n)` the motive is `A`, so the result needs no default value:

  ```lisp
  (def vhead (pi {A (sort 1)} (pi {n Nat} (pi v (Vec A (succ n)) A)))
    (lam {A} (sort 1) (lam {n} Nat (lam v (Vec A (succ n))
      (match v (motive (lam k Nat (lam w (Vec A k)
                         (match k (sort 1) (case (zero) Unit) (case (succ k1 ih) A)))))
        (case (vnil) unit)
        (case (vcons h t ih) h))))))
  ```
* **Operations.** `vappend : Vec A n -> Vec A m -> Vec A (add n m)`, `vsnoc : Vec A n -> A ->
  Vec A (succ n)`, `vreverse : Vec A n -> Vec A n` (via `vsnoc`), `vmap : (A -> B) -> Vec A n ->
  Vec B n`, `vtail : Vec A (succ n) -> Vec A n`, `vto_list : Vec A n -> List A`, `vsum : Vec Nat n
  -> Nat`, and `vlength : Vec A n -> Nat`, which returns the index `n` without traversing the
  vector. All are total (`def`), for every element type `A`.
* **Ownership in the same definitions.** Elements of a generic `A` are not Copy, so each
  operation uses each element at most once. `vappend`'s second vector and `vsnoc`'s new element are
  `#[once]` parameters, consumed in the `vnil` case only (`vnil` is not a repeated case). In
  `vmap` the `vcons` case, which runs once per element, calls the captured function, so the
  function's type is an `Fn` type; with a `#[once]` function type the definition is rejected
  (`neg/vectors_vmap_fnonce.lrl`, `F0206 Function kind mismatch: expected Fn, got FnOnce`). Values
  may be dropped (affine): `vtail` drops the head.
* **Proofs.** `cong`, `sym` and `trans` are proved for `Eq` (prelude: `Eq A x y` is a `(sort 0)`
  proposition with constructor `refl`) by dependent matches on the equality proof. `cong` takes
  its function at the most permissive kind, `(pi #[once] x A B)`; the file passes it a
  partially applied constructor (`vcons h`), a global function (`vreverse`) and a `#[once]`
  lambda. The lemma `vreverse_vsnoc : vreverse (vsnoc v x) = vcons x (vreverse v)` and the
  involution

  ```lisp
  (def vreverse_involutive (pi {A (sort 1)} (pi {n Nat} (pi v (Vec A n)
                             (Eq (Vec A n) (vreverse (vreverse v)) v))))
    (lam {A} (sort 1) (lam {n} Nat (lam v (Vec A n)
      (match v (motive (lam k Nat (lam w (Vec A k) (Eq (Vec A k) (vreverse (vreverse w)) w))))
        (case (vnil) (refl (Vec A zero) vnil))
        (case (vcons h t ih) (trans (vreverse_vsnoc (vreverse t) h) (cong (vcons h) ih))))))))
  ```

  are proved by induction on the vector, for every `A`, `n` and `v`. The step of the involution:
  `vreverse (vreverse (vcons h t))` computes to `vreverse (vsnoc (vreverse t) h)`, which
  `vreverse_vsnoc` rewrites to `vcons h (vreverse (vreverse t))`, which the induction hypothesis
  under `cong (vcons h)` rewrites to `vcons h t`; `trans` chains the two steps. The step of
  `vreverse_vsnoc` is the induction hypothesis under `cong (lam #[once] u (Vec A _) (vsnoc u h))`
  (the hole `_` is the length of the tail, which a case pattern cannot name: it is an implicit
  field of `vcons`). The corollary `vreverse_injective` (from `vreverse v = vreverse w` to `v = w`)
  uses `sym`, `cong` and `trans`, and `v3_reverse_twice` instantiates the theorem at a concrete
  vector. The equality toolkit and the theorems (from `(def cong` up to `(def v3`) take 33
  non-blank, non-comment lines.
* **No axioms, total definitions.** All theorems are ordinary `def`s (total; not `noncomputable`,
  not `unsafe`). When the kernel admits a definition it records the axioms the definition depends
  on, transitively (`collect_axioms_rec` in `add_definition`, `kernel/src/checker.rs`), and
  rejects a `def` (neither `noncomputable` nor `unsafe`) with a non-empty set (`K0023`); the CLI
  prints `Definition '...' depends on axioms: ...` for admitted definitions with axioms. For
  `vectors.lrl`, `lrl run` and `lrl --require-axiom-tags run` print nothing and exit 0, and the
  kernel-only harness (below) reports `statement_sort=Prop totality=Total noncomputable=false
  axioms=[]` for every theorem (the kernel infers `Sort 0` for each statement, so each value is a
  proof) and re-checks each value against its statement with the kernel type checker.
* **False proofs are rejected.** Through the CLI, the false lemma `vreverse (vsnoc v x) = vcons x
  v` (with the proof of the true lemma) and the false equation `vreverse [1, 2] = [1, 2]` (by
  `refl`) are rejected by the elaborator (`F0214`), before the kernel is reached. The harness
  `case_studies/tools/vectors_kernel_check` submits false statements to the kernel directly
  (`Env::add_definition`, elaborator bypassed): the admitted proof terms of `vreverse_vsnoc` and
  `vreverse_involutive` paired with false statements, and `refl [1, 2]` for `vreverse [1, 2] = [1,
  2]`, are all rejected with `K0002` (type mismatch), and the same values with the true statements
  are accepted.

`main` builds `v3 = [1, 2, 3]` and prints `vhead v3` (1), `vhead (vreverse v3)` (3),
`vsum (vreverse v3)` (6), `vsum (vtail v3)` (5), `vsum (vmap (lam x (nat_mul x ten)) v3)` (60, the
closure captures `ten`) and `length (vto_list (vreverse v3))` (3), and returns `vlength (vappend v3 v3)`,
6, read from the index.

### Files

| File | Content |
|---|---|
| `vectors.lrl` | the complete program |
| `neg/vectors_vhead_vnil.lrl` | `vhead` applied to `vnil` |
| `neg/vectors_vappend_wrong_index.lrl` | a `vappend` whose `vcons` case drops the head (result one element short of its index) |
| `neg/vectors_vappend_wrong_length.lrl` | `vappend v2 v2` declared as a `Vec Nat 3` |
| `neg/vectors_false_vreverse_vsnoc.lrl` | the false lemma `vreverse (vsnoc v x) = vcons x v`, with the proof of the true lemma |
| `neg/vectors_false_reverse_concrete.lrl` | the false equation `vreverse [1, 2] = [1, 2]`, by `refl` |
| `neg/vectors_vmap_fnonce.lrl` | `vmap` with a `#[once]` function type |
| `neg/vectors_vtail_direct_generic.lrl` | the direct `vtail` (cons case returns the tail) for a generic element type: the reason `vtail` goes through a split |
| `run_vectors.sh` | reruns all of the above and the kernel-only checks, and writes `results_vectors.md` |
| `results_vectors.md` | the observed results (generated) |
| `../tools/vectors_kernel_check/` | kernel-only harness (a cargo project, not a workspace member; public APIs only) |

As in case B, each file under `neg/` repeats the declarations it needs from `vectors.lrl`
(without comments) above a `;; ---- new code ----` line; `run_vectors.sh` checks that they are
copies of top-level forms of `vectors.lrl`, and also runs a corrected copy of every variant (the
fault removed by one `sed` edit of the new code), which must be accepted.
`cli/tests/case_studies.rs` checks the program's output under both backends and the code of every
negative variant.

### How to run

```sh
case_studies/lrl/run_vectors.sh                   # builds the CLI unless LRL=<cli binary> is set
lrl run case_studies/lrl/vectors.lrl              # checks everything; prints nothing
lrl run case_studies/lrl/vectors.lrl --backend typed
lrl compile case_studies/lrl/vectors.lrl --backend dynamic -o build/vectors && build/vectors
cargo run --manifest-path case_studies/tools/vectors_kernel_check/Cargo.toml -- case_studies/lrl/vectors.lrl
```

### Observed results

From `results_vectors.md` (CLI binary sha256 prefix recorded there):

| Command | Outcome |
|---|---|
| `lrl run vectors.lrl` | accepted (exit 0), no output: no diagnostic, no axiom-dependency warning |
| `lrl --require-axiom-tags run vectors.lrl` | accepted (exit 0), no output |
| `lrl run vectors.lrl --backend typed` | prints `1`, `3`, `6`, `5`, `60`, `3`, then `Result: 6` |
| `lrl compile vectors.lrl --backend typed` (also `--backend auto`, no fallback), binary | prints `1`, `3`, `6`, `5`, `60`, `3`, then `Result: 6` |
| `lrl compile vectors.lrl --backend dynamic`, binary | prints `1`, `3`, `6`, `5`, `60`, `3`, then `Result: Nat(6)` |

| Negative variant | Code | Message (as printed) |
|---|---|---|
| `vectors_vhead_vnil.lrl` | F0214 | `Elaboration error (Value) in 'head_of_empty': Unification failed: Nat.zero vs (Nat.succ ?m1)` |
| `vectors_vappend_wrong_index.lrl` | F0214 | `Elaboration error (Value) in 'vappend': Unification failed: (rec.Nat.{1} ... _implicit0) vs (Nat.succ (rec.Nat.{1} ... _implicit0))` (`add k m` vs `succ (add k m)`, unfolded) |
| `vectors_vappend_wrong_length.lrl` | F0214 | `Elaboration error (Value) in 'v3_claimed': Unification failed: (rec.Nat.{1} ...) vs (Nat.succ (Nat.succ (Nat.succ Nat.zero)))` (`add 2 2` vs `3`) |
| `vectors_false_vreverse_vsnoc.lrl` | F0214 | `Elaboration error (Value) in 'vreverse_vsnoc_wrong': Unification failed: (rec.Vec.{1} ...` |
| `vectors_false_reverse_concrete.lrl` | F0214 | `Elaboration error (Value) in 'reverse_is_identity_on_12': Unification failed: (Eq (Vec Nat ..) ...` |
| `vectors_vmap_fnonce.lrl` | F0206 | `Elaboration error (Value) in 'vmap_once': Function kind mismatch: expected Fn, got FnOnce` |
| `vectors_vtail_direct_generic.lrl` | K0021 | `Environment error defining 'vtail_direct': Ownership violation [RecursiveFieldConsumedByIh]: recursive field 't' is not Copy and was consumed to compute its induction hypothesis; use the induction hypothesis instead` |

Every negative variant exits with status 1, and every corrected copy is accepted (exit 0, no
error). The length errors, the false proofs and the kind error are found by the elaborator
(`F0214`, `F0206`) before the kernel is reached; the `K0021` error is raised by the kernel's
ownership check when the definition is added to the environment.

Kernel-only checks (`vectors_kernel_check`, exit 0, `FAILURES 0`): `vectors.lrl` is processed
with no diagnostic; for `cong`, `sym`, `trans`, `vreverse_vsnoc`, `vreverse_involutive`,
`vreverse_injective` and `v3_reverse_twice` it prints `statement_sort=Prop totality=Total
noncomputable=false axioms=[] kernel_recheck=ok` (`statement_sort` is the sort the kernel infers
for the statement; as a control, the types of the program definitions `vhead` and `vreverse`
are reported as `Sort(Succ(Succ(Zero)))`, not `Prop`). Submitted directly to the kernel (`Env::add_definition` on a copy
of the environment): the admitted proof of `vreverse_vsnoc` with the statement `vreverse (vsnoc v
x) = vcons x v`, the admitted proof of `vreverse_involutive` with the statement `vreverse
(vreverse v) = vreverse v`, and `refl [1, 2]` with the statement `vreverse [1, 2] = [1, 2]` are
each rejected with `K0002 Type mismatch`; the same three values with the true statements are
accepted.

### Why `vtail` goes through a split, and compiler problems found

* **`vtail` through a split of the vector** (a consequence of the recursor rule, by design; see
  the note above `VSplit` in `vectors.lrl`). The direct
  definition (`neg/vectors_vtail_direct_generic.lrl`) is rejected by the kernel for a generic
  element type: the recursor computes the induction hypothesis of the tail eagerly, which
  consumes the tail, so the case cannot also return it (`K0021 RecursiveFieldConsumedByIh`; with
  `Vec Nat` the same definition is accepted, as `Nat` is Copy). LRL has no case-analysis
  eliminator without induction hypotheses (only recursors). `vtail` therefore computes, by
  recursion, the head as a vector of length `min1 k` and the tail (`VSplit A k`), rebuilding the
  next tail from the induction hypothesis (`vjoin`); it costs O(n) instead of O(1).

The first version of this case study needed three workarounds and could not be compiled with
the typed backend, because of compiler bugs found while writing it. They have been fixed
(regression tests in `cli/tests/case_study_regressions.rs`; the program now uses none of the
workarounds):

* *(was W1)* Implicit arguments under a binder of a definition's type or in a `match` motive were
  not inferred (`[K0047] ... Unresolved metavariable ?0`, bug W_A_vectors_1): the statements had to
  read `(vreverse {A} {n} (vreverse {A} {n} v))`.
* *(was W2)* Constraints postponed before the implicit arguments were known were retried without
  substituting their solutions (`F0214`/`F0217`, bug W_A_vectors_2), and a lambda whose body still
  contained such an argument got the wrong function kind (`F0206`, bug W_A_vectors_3): each
  inductive step was a separate lemma with every implicit argument written out
  (`vreverse_vsnoc_step`, `vreverse_involutive_step`, `cong_vsnoc`, `vsplit_cons`).
* *(was W4)* `vmap` with a captured function was rejected by MIR (`M100`, bug W_A_vectors_9) and
  passed its function down the recursion instead.
* Typed backend: the recursor of `vhead` (a large elimination) failed in rustc (`E0308`), and
  `VSplit`'s `Nat` parameter was given a `()` constructor argument (`E0308`, bug W_A_vectors_7).
  Two other encodings of `vtail` failed after the kernel had accepted them: a head typed by a large
  elimination was rejected by MIR typing (`M300`, bug W_A_vectors_4), and a type application
  passed as an argument (`Vec A 1` to the prelude's `Pair`) made the compiled program panic at
  run time (bug W_A_vectors_6). A function with `#[once]` type binders, such as the prelude's
  `pair_fst`, could not be called with the typed backend (`E0283`, bug W_A_vectors_8).

### What is not shown

* **Cost.** No time or size is claimed here. `vtail` is O(n) by construction (through the split). How long the
  kernel takes to check the proofs has not been measured.
* **Proof automation.** Proofs are explicit terms; there are no tactics, and definitional
  unfolding is all the automation there is (the `vnil` cases are `refl`, the `vcons` cases are
  `cong`/`trans` steps).

### Audit note (case study A)

* All outputs in "Observed results": `LRL=<CLI binary> case_studies/lrl/run_vectors.sh`, which
  wrote `results_vectors.md` (binary sha256 prefix and date recorded there; 7/7 negative rows
  `Match = yes`; 7/7 corrected copies exit 0 with no error; "Copied declarations": all 7 variant
  files consistent; kernel-only checks exit 0, `FAILURES 0`).
* The first version of the case study (with the workarounds W1, W2, W4 and the typed-backend
  failures described above) was checked with a CLI built before the fixes (sha256 prefix
  `f3bdd0fd32004822`); each bug W_A_vectors_1 to _9 has a minimal reproduction that was run with
  that binary and again after the fixes.
* Identifiers and paths cited (`collect_axioms_rec`, `add_definition`, `K0023`, `K0002`,
  `kernel::checker::check`) were found with `grep -n` in `kernel/src/checker.rs`. "Only
  recursors": `grep -rn -i -E 'casesOn|cases_on' kernel/src frontend/src` finds nothing. "The
  prelude has no `Unit`, `Vec` or `Fin`": `grep -rn -E 'inductive (copy )?(\([a-z_ ]+\) )?(Unit|Vec|Fin) ' stdlib`
  finds nothing.
* `vectors.lrl` has 104 non-blank, non-comment lines
  (`grep -v -E '^\s*;' case_studies/lrl/vectors.lrl | grep -v -E '^\s*$' | wc -l`), 24 top-level
  forms (`grep -c -E '^\((def|inductive) ' case_studies/lrl/vectors.lrl`); the equality toolkit
  and the theorems, from `(def cong` up to `(def v3`, have 33 such lines
  (`awk '/^\(def cong /{f=1} /^\(def v3 /{f=0} f' case_studies/lrl/vectors.lrl | grep -v -E '^\s*;' | grep -v -E '^\s*$' | wc -l`).

## B. A protocol channel tied to a vector (`protocol.lrl`)

### What the program shows

`protocol.lrl` (the paper's running example) combines the three features in one program:

* **Dependent types.** `Chan n` is a channel on which exactly `n` more messages may be sent.
  The operations generated by `defsend` have type `{n : Nat} -> Chan (succ n) -> P -> Chan n`,
  and `close : Chan zero -> Receipt`. `send_all : {n} -> Vec Nat n -> Chan n -> Receipt` sends
  every element of a vector and closes the channel; the vector's length and the protocol's
  length are the same `n`. It is a dependent elimination of the vector with the motive
  `k, _ |-> (Chan k -> Receipt)`:

  ```lisp
  (def send_all (pi {n Nat} (pi v (Vec Nat n) (pi #[once] c (Chan n) Receipt)))
    (lam {n} Nat (lam v (Vec Nat n)
      (match v (motive (lam k Nat (lam w (Vec Nat k) (pi #[once] c (Chan k) Receipt))))
        (case (vnil) close)
        (case (vcons h t ih) (lam #[once] c (Chan (succ _)) (ih (send c h))))))))
  ```
* **Ownership.** `Chan` is declared `(affine)`, so no Copy instance is derived for it: every
  operation consumes its channel and returns the channel for the next state. A second use of
  a consumed channel is rejected by the kernel's ownership check (`K0021`). The function
  returned by `send` after the channel argument owns the channel, so its kind is `#[once]`
  (FnOnce); so are the motive of `send_all` and the closure built in its `vcons` case (it
  consumes `c` and calls the FnOnce induction hypothesis). `send_checked` is a branching step
  that consumes the channel in both branches of a match on `Bool`: `Bool` is not recursive, so
  the cases are alternatives and each may move the channel.
* **Hygienic macros.** `send` and `send_bit` are generated by the macro
  `(defsend NAME PAYLOAD ENCODE)`. Its template binds `n`, `c`, `x` and `log`. The program
  defines a user function that is also called `log` (it prints a message) and passes it as
  `ENCODE`: `(defsend send Nat log)`. In the expansion, the argument `log` still denotes the
  user's function, not the template's pattern variable `log : List Nat`; `send` prints every
  message it sends. Pasting the expansion printed by `lrl --expand-full` as ordinary source
  text (`neg/protocol_capture_by_hand.lrl`, where the two names do collide) is rejected with a
  type error.

`main` runs two sessions: a channel for 3 messages fed by the vector `[7, 8, 9]`, and a
2-message channel driven by `send_checked` (one valid reading 5, one invalid reading replaced
by a 0 flag). It prints the sent messages `7 8 9 5` and returns the sum of both receipts' logs,
29.

### Files

| File | Content |
|---|---|
| `protocol.lrl` | the complete program |
| `neg/protocol_send_twice.lrl` | sends twice on the same channel value |
| `neg/protocol_send_twice_macro.lrl` | the same double use, produced by a macro whose template mentions its channel argument twice |
| `neg/protocol_use_after_branch.lrl` | uses the channel after a branch of a `Bool` match consumed it |
| `neg/protocol_send_on_closed.lrl` | sends on a `Chan zero` |
| `neg/protocol_close_early.lrl` | closes a channel that still has a message to send |
| `neg/protocol_send_all_wrong_length.lrl` | `send_all` with a 2-element vector and a `Chan 3` |
| `neg/protocol_capture_by_hand.lrl` | the expansion of `(defsend send Nat log)` pasted as text: `log` is captured |
| `neg/protocol_send_not_once.lrl` | `defsend` without `#[once]`: the closure that owns the channel is declared `Fn` |
| `limits/protocol_drop_unclosed.lrl` | ACCEPTED: a channel is dropped before it is closed |
| `limits/protocol_reindex.lrl` | ACCEPTED: a used-up `Chan zero` is rebuilt with `mk_chan` at another index |
| `run_protocol.sh` | reruns all of the above and writes `results_protocol.md` |
| `results_protocol.md` | the observed results (generated) |

Each file under `neg/` and `limits/` repeats the declarations it needs from `protocol.lrl`
(without comments) above a `;; ---- new code ----` line; `run_protocol.sh` checks that they are
copies of top-level forms of `protocol.lrl`.

### How to run

```sh
case_studies/lrl/run_protocol.sh                  # builds the CLI unless LRL=<cli binary> is set
lrl compile case_studies/lrl/protocol.lrl --backend dynamic -o build/protocol && build/protocol
lrl run case_studies/lrl/protocol.lrl --backend typed
lrl run case_studies/lrl/neg/protocol_send_twice.lrl
```

`lrl run <file>` without `--backend typed` checks every definition (elaboration, kernel, MIR)
but does not execute `main`; use `compile` or `run --backend typed` to run the program.

### Observed results

From `results_protocol.md` (CLI binary sha256 prefix recorded there):

| Command | Outcome |
|---|---|
| `lrl run protocol.lrl` | accepted (exit 0) |
| `lrl run protocol.lrl --backend typed` | prints `7`, `8`, `9`, `5`, then `Result: 29` |
| `lrl compile protocol.lrl --backend typed`, binary (also `--backend auto`: no fallback) | prints `7`, `8`, `9`, `5`, then `Result: 29` |
| `lrl compile protocol.lrl --backend dynamic`, binary | prints `7`, `8`, `9`, `5`, then `Result: Nat(29)` |

| Negative variant | Code | Message (as printed) |
|---|---|---|
| `protocol_send_twice.lrl` | K0021 | `Environment error defining 'replay': Ownership violation [UseAfterMove]: variable 'c' is used after it was moved` |
| `protocol_send_twice_macro.lrl` | K0021 | `Environment error defining 'retry': Ownership violation [UseAfterMove]: variable 'c' is used after it was moved`, with the label `macro 'send-and-retry' expanded here` on the call `(send-and-retry c 7)` |
| `protocol_use_after_branch.lrl` | K0021 | `Environment error defining 'after_branch': Ownership violation [UseAfterMove]: variable 'c' is used after it was moved` |
| `protocol_send_on_closed.lrl` | F0214 | `Elaboration error (Value) in 'extra': Unification failed: Nat.zero vs (Nat.succ ?m0)` |
| `protocol_close_early.lrl` | F0214 | `Elaboration error (Value) in 'early': Unification failed: (Nat.succ Nat.zero) vs Nat.zero` |
| `protocol_send_all_wrong_length.lrl` | F0214 | `Elaboration error (Value) in 'short': Unification failed: (Nat.succ Nat.zero) vs Nat.zero` |
| `protocol_capture_by_hand.lrl` | K0003 | `Elaboration error (Value) in 'send': Type inference failed during elaboration: Expected function type, got App(Ind("List", []), Ind("Nat", []))` |
| `protocol_send_not_once.lrl` | F0206 | `Elaboration error (Value) in 'send': Function kind mismatch: expected Fn, got FnOnce`, with the label `in code produced by macro 'defsend'` |

Every negative variant exits with status 1. Where the errors come from: the `K0021` errors are
raised when the definition is added to the kernel environment (`env.add_definition`,
`cli/src/driver.rs`, whose ownership walk is `check_ownership_in_term`,
`kernel/src/checker.rs`); the macro-produced double use gets the same error as the hand-written
one, plus the macro label. The `K0021` message names the variable, but its source span is the
whole body of the definition, not the position of the second use. The protocol-state errors
(wrong number of sends, wrong vector length) are type errors found by the elaborator
(`F0214`) before the kernel is reached. Each variant becomes accepted when its fault is
removed: `run_protocol.sh` runs a corrected copy of every negative variant (one `sed` edit of the
new code; table "Corrected copies" in `results_protocol.md`), and each must exit 0 without an error.

### Compiler problems found by this case study (fixed)

No workaround remains in `protocol.lrl`. Two compiler bugs were found while writing it and have
been fixed (regression tests in `cli/tests/case_study_regressions.rs` and `cli/tests/case_studies.rs`):

* **A Copy field read out of an affine value** (bug W_B_protocol_1). With the log as a `List Nat`
  field, a match reading the field out of an affine `Chan` was rejected by MIR (`[M300] ... Copy of
  non-Copy place ... has type Adt(AdtId(List, ...), [Nat])` and `[M101] ...`): lowering copies the
  field because `List Nat` is Copy, but MIR's checks treated every inductive-typed projection of a
  non-Copy value as non-Copy (`MirType::is_copy` is `false` for `Adt`). MIR now decides Copy-ness
  of inductive types with the kernel's Copy instances (`AdtLayoutRegistry::type_is_copy` in
  `mir/src/types.rs`, used by `check_operand_copy` and the ownership pass). Until then the program
  used an `affine` list type `Log` of its own in place of `List Nat`.
* **Typed backend, value parameter** (bug W_B_protocol_2). The kernel infers the number of
  parameters of an inductive from its constructors (`infer_num_params_from_ctors`,
  `kernel/src/checker.rs`): because the only constructor `mk_chan` returns `Chan n` for its own
  binder `n`, `n` is a *parameter* of `Chan` (a value parameter), not an index. The typed backend
  emitted the constructor with a `()` argument for it while its uses passed a `u64` (rustc `E0308`),
  and `--backend auto` fell back to the dynamic backend. Value parameters now keep their type in
  constructor signatures.

### What is not enforced

* **Affine, not linear.** A channel can be dropped without being closed:
  `limits/protocol_drop_unclosed.lrl` sends one message on a 2-message channel and discards the
  rest; it is accepted and runs (prints `7`, `Result: Nat(0)`). The types guarantee that a
  channel value is used at most once and that a channel opened with `open_chan n` can be passed
  to `close` only after exactly `n` sends; they do not guarantee that `close` is reached.
* **No abstraction boundary.** LRL has no private constructors: any code can match on a `Chan`
  and rebuild it with `mk_chan` at another index. `limits/protocol_reindex.lrl` turns a
  `Chan zero` into a `Chan 5` and sends 6 messages in total on a channel opened for 1; it is
  accepted and runs (prints `1` to `6`, `Result: Nat(6)`). The protocol guarantee holds for code
  that uses only `open_chan`, the generated send operations and `close`.
* **Hygiene covers local binders only.** The free names of the `defsend` template (`Chan`,
  `mk_chan`, `cons`, `Nat`, `succ`) are resolved where the macro is used, not where it is
  defined (documented in `docs/spec/macro_system.md`, "Limits of hygiene"; not exercised by
  these files).

### Audit note (case study B)

Facts in this section were produced with a CLI built from the working tree, run from the
repository root:
* All outputs above: `LRL=<that binary> case_studies/lrl/run_protocol.sh`, which wrote
  `results_protocol.md` (sha256 prefix of the binary recorded there; every negative row
  `Match = yes`; "Copied declarations": all 10 variant files consistent).
* An earlier version of this case study (binary with sha256 prefix `f3bdd0fd32004822`, before the
  two fixes above) used the `Log` workaround; with it, the typed backend failed with 3 x rustc
  `E0308` (`expected struct Rc<dyn LrlCallable<u64, Rc<(dyn LrlCallable<Log, Chan<()>> + 'static)>>>`,
  `found struct Rc<(dyn LrlCallable<(), Rc<(dyn LrlCallable<Log, Chan<_>> + 'static)>> + 'static)>`)
  and `protocol_send_on_closed.lrl` was reported as `F0217` (an unsolved constraint) instead of
  `F0214`.
* "Each variant becomes accepted when its fault is removed": `run_protocol.sh` builds a
  corrected copy of each of the 8 negative variants (`fix_variant` in the script) and runs it
  with `lrl run`; the "Corrected copies" table of `results_protocol.md` records the exit status
  and the number of `Error` lines of each.
* `n` is a parameter of `Chan`: a match on a value of the same shape of type `(Ch 3)` with the
  motive `(lam w (Ch 3) Nat)` (no index binder) is accepted, while a motive over one index is
  rejected with `F0205 ... expected a match motive over 0 index argument(s) ...`.
* Identifiers and paths cited (`env.add_definition` in `cli/src/driver.rs`,
  `check_ownership_in_term`, `infer_num_params_from_ctors`, `check_operand_copy`,
  `MirType::is_copy`, `AdtLayoutRegistry::type_is_copy`, "Limits of hygiene") were found with
  `grep -n` in the cited files.
* `protocol.lrl` has 40 non-blank, non-comment lines
  (`grep -v -E '^\s*;' case_studies/lrl/protocol.lrl | grep -v -E '^\s*$' | wc -l`).
