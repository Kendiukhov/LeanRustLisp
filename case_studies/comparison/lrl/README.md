# LRL comparison programs

Small, self-contained LRL programs, one file per case. Each one tests one property of the
comparison (Q1 to Q12) exactly as the Lean 4, Idris 2, Rust and Racket programs next to this
directory do (see their READMEs and `../results_lean_idris.md`, `../results_rust_racket.md`).
The observed outcome of every file is recorded in `../results_lrl.md`; `../SUMMARY.md` puts all
five languages side by side.

## Conventions

- `qNN_name.lrl` is a positive program (a correct program that uses the feature);
  `qNN_name__variant.lrl` is a variant, usually a negative one (the property is violated). A
  variant is a complete copy of its positive program; the changed lines are marked `CHANGED`.
- The program entry is the last top-level `def` (`main`). `print_nat` prints one number per line;
  the compiled binary then prints `Result: <value of main>` (`Result: Nat(..)` for the dynamic
  backend).
- `q08_macro_global_names_lib.lrl` is a macro library imported by the two
  `q08_macro_global_names*.lrl` programs; it is not a case by itself.

Run everything and regenerate the results table (from any directory; the script runs the CLI
from the repository root, because the CLI finds `stdlib/` relative to its working directory):

```sh
LRL_BIN=/path/to/lrl CMP_BUILD_DIR=/some/tmp/dir case_studies/comparison/run_lrl.sh
```

Without `LRL_BIN` the script builds the CLI with `cargo build -p cli`. Or compile one case by hand,
from the repository root:

```sh
cargo run -p cli -- compile case_studies/comparison/lrl/q05_single_use_channel__reuse.lrl --backend dynamic -o /tmp/q05
```

Every case is compiled with both backends: `--backend typed` (LRL types mapped to Rust types) and
`--backend dynamic` (Rust over a universal `Value` type). Both run the same checks (elaborator,
kernel, MIR typing / ownership / NLL borrow checking) before code generation. `lrl compile`
writes the generated Rust to the repository's git-ignored `build/` directory; the evidence rows
`[generated Rust: ...]` of the results table quote it. Evidence rows of kind `limit` record, as an
observed outcome, what LRL cannot express at all: `NOT_IN_PLACE` (Q11: the generated cons
constructor allocates a new cell) and `NO_OPERATION_ON_REF` (Q9: no stdlib declaration takes a
`Ref` argument); `../SUMMARY.md` shows them as "not expressible".

## Files

| File | Q | Kind | What it shows |
|---|---|---|---|
| `q01_head.lrl` | Q1 | positive | `Vec A n` and a total `vhead : Vec A (succ n) -> A`: a dependent match whose motive is `Unit` at index zero and `A` at a successor, so the impossible `vnil` case returns `unit`; no run-time check, no default value. |
| `q01_head__empty.lrl` | Q1 | negative | `vhead` of an empty vector: type error. |
| `q01_head__any_length.lrl` | Q1 | negative | a `head` on `Vec A n` for every `n` (constant motive `A`): the `vnil` case has no `A` to return; type error. |
| `q02_append.lrl` | Q2 | positive | `vappend : Vec A n -> Vec A m -> Vec A (add n m)`; the result of appending a 2- and a 3-vector is given the type `Vec Nat 5`. |
| `q02_append__wrong_len.lrl` | Q2 | negative | the caller claims the result is a `Vec Nat 4`: type error. |
| `q02_append__drop_elem.lrl` | Q2 | negative | the cons case forgets the element: type error. |
| `q03_reverse_involution.lrl` | Q3 | positive | list `rev` (via `snoc`) and kernel-checked proofs, by induction, of `rev (snoc l x) = cons x (rev l)` and `rev (rev l) = l` for every element type and list, using `cong` and `trans` proved in the same file. No axioms: a total `def` that depends on an axiom is rejected (K0023, see `q04_erasure__forge.lrl`). |
| `q03_reverse_involution__buggy.lrl` | Q3 | negative | the same proofs for a `rev` that drops elements: rejected. |
| `q03_reverse_involution__false_law.lrl` | Q3 | negative | a "proof" of the false law `rev l = l`: rejected. |
| `q04_erasure.lrl` | Q4 | positive | `safe_div` takes a proof (`Eq Bool (nat_is_zero b) false`, a proposition); the call passes `refl`. Evidence rows quote the generated Rust of `safe_div` (the proof becomes a `()` argument) and of `Vec` (each `vcons` cell stores its length index). |
| `q04_erasure__zero_divisor.lrl` | Q4 | negative | divisor 0 with the proof `refl`: type error. |
| `q04_erasure__forge.lrl` | Q4 | negative | the proof is forged with an `axiom`: a total `def` may not depend on an axiom (K0023). |
| `q04_erasure__index_at_runtime.lrl` | Q4 | negative | the length index of a `Vec` (an implicit argument) is returned as a run-time value: accepted, the index is not erased. |
| `q05_single_use_channel.lrl` | Q5 | positive | an `affine` channel (holding a `List Nat` log of sent messages) consumed by `send`, which returns a receipt with the log. |
| `q05_single_use_channel__reuse.lrl` | Q5 | negative | a second `send` on the consumed channel: use after move (K0021). |
| `q06_typestate.lrl` | Q6 | positive | `Chan Open` / `Chan Closed` typestate (affine, with a `List Nat` log): `send`, `close`, `finish` (returns the log). |
| `q06_typestate__send_after_close.lrl`, `q06_typestate__close_twice.lrl` | Q6 | negative | `send` / `close` on a closed channel: type error. |
| `q07_protocol_length.lrl` | Q7 | positive | `Chan n` (affine, with a `List Nat` log) counts the messages still to send; `send_all : Vec Nat n -> Chan n -> List Nat` by dependent elimination of the vector with the motive `(pi #[once] c (Chan k) (List Nat))`: the `vcons` case returns a once-only closure that sends the head and calls the induction hypothesis; `close` returns the log. Also a written-out sequence of two sends. |
| `q07_protocol_length__too_many.lrl`, `__too_few.lrl` | Q7 | negative | one send too many / too few: type error. |
| `q07_protocol_length__len_mismatch.lrl` | Q7 | negative | `send_all` with a 2-vector on a `Chan 3`: type error. |
| `q07_protocol_length__skip_send.lrl` | Q7 | negative | `send_all`'s `vcons` case forgets to send: type error. |
| `q07_protocol_length__abandon.lrl` | Q7 | negative | a channel with one message owed is never closed: accepted (affine, not linear). |
| `q08_macro_hygiene.lrl` | Q8 | positive | macros `defunit` / `defadd` / `defval` generate a unit type (an `inductive`) and its typed operations (`def`s) for Meters and Seconds; `with_tmp`'s template binder `tmp` does not capture the user's `tmp` (101 = hygienic, 200 = captured). |
| `q08_macro_hygiene__mix_units.lrl` | Q8 | negative | a Meters value passed to the generated `seconds_add`: type error. |
| `q08_macro_global_names.lrl` | Q8 | positive | a global name (`helper`) in an imported macro's template: resolved at the use site (the client's `helper` = 2, not the library's = 1), and a local binder `helper` at the call site does not capture it. |
| `q08_macro_global_names__lib_only.lrl` | Q8 | positive | the same macro in a client without its own `helper`: rejected (`Unbound variable: helper`); `import-macros` imports a file's macros but not its definitions, so a template cannot refer to its library's own definitions. |
| `q09_two_mut_refs.lrl` | Q9 | positive | `(&mut x)` and `(&mut y)` passed to one call; two `&mut x` whose lifetimes do not overlap (NLL). Limit rows `[stdlib: declarations mentioning Ref]` (one per backend): the stdlib declarations that mention `Ref` are `Ref`, `borrow_shared` and `borrow_mut`, and none takes a `Ref` argument, so nothing reads or writes through a reference (`NO_OPERATION_ON_REF`). |
| `q09_two_mut_refs__alias_call.lrl` | Q9 | negative | `(touch2 (&mut x) (&mut x))`: rejected by the MIR borrow checker (M200). |
| `q09_two_mut_refs__alias_live.lrl` | Q9 | negative | a second `&mut x` while the first is live: M200. |
| `q10_consume_both_branches.lrl` | Q10 | positive | an affine token consumed in both branches of a match on `Bool` and in all three branches of a match on a three-constructor type. |
| `q10_consume_both_branches__one_branch.lrl` | Q10 | positive | consumed in one branch only: accepted (affine). |
| `q10_consume_both_branches__use_after.lrl` | Q10 | negative | used again after the match: use after move (K0021). |
| `q11_inplace_reverse.lrl` | Q11 | positive | a reverse of a list of affine tokens that consumes its input. LRL has no in-place update; the limit rows quote the generated Rust of both backends: the cons constructor allocates a new cell (`NOT_IN_PLACE`), and the typed recursor clones the tail. |
| `q11_inplace_reverse__use_after_move.lrl` | Q11 | negative | the old list is used after `rev` consumed it: use after move (K0021). |
| `q12_fnonce_twice.lrl` | Q12 | positive | a `#[once]` closure that consumes a captured affine token, called once; a `#[once]` function argument called once. |
| `q12_fnonce_twice__call_twice.lrl` | Q12 | negative | the once-only closure called twice: use after move (K0021). |
| `q12_fnonce_twice__as_fn.lrl` | Q12 | negative | a consuming closure passed where a `#[fn]` (repeatable) function is required: kind mismatch (F0206). |
| `q12_fnonce_twice__in_loop.lrl` | Q12 | negative | the recursive (`succ`) case of a recursion consumes a captured token: `ConsumedInRepeatedScope` (K0021). |

## What LRL could and could not do here (observed; see `../results_lrl.md`)

- Rejected before running: an empty vector passed to the total head and a head for every length
  (Q1), wrong lengths in `vappend` (Q2), proofs about a wrong reverse and a false law (Q3), a wrong
  proof argument and a proof forged with an axiom (Q4), reuse of a consumed channel (Q5), a call
  in the wrong protocol state (Q6), one message too many or too few, a length mismatch and a
  skipped send, also inside the generic `send_all` (Q7), a macro-generated operation used at the
  wrong type (Q8), two live mutable borrows of one variable (Q9), use of a value after a match
  consumed it in every branch (Q10) or after `rev` consumed it (Q11), and a once-only closure
  called twice, used where a repeatable function is required, or consumed by a recursive case
  (Q12). Type errors come from the elaborator (F0214, F0217), uses after a move and consumption in
  a repeated scope from the kernel (K0021, which names the variable), axiom dependence from the
  kernel environment (K0023), the function-kind mismatch from the elaborator (F0206), and the
  borrow conflicts from MIR's borrow checker (M200).
- Not detected, by design: abandoning a channel that still owes a message (Q7 `__abandon`) and
  consuming a token in one branch only (Q10 `__one_branch`). The ownership discipline is affine,
  like Rust's, not linear like Idris 2's quantity 1 or Turnstile `lin`.
- Not erased: the length index of `Vec` is an ordinary implicit run-time argument. It is stored in
  every `vcons` cell of the typed backend (`enum lrl_Vec<T0> { vnil, vcons(u64, T0, ...) }`) and a
  function can return it (Q4 `__index_at_runtime` is accepted). A proof argument becomes a `()`
  argument that is still passed (`fn safe_div() -> Rc<dyn LrlCallable<u64, Rc<dyn LrlCallable<u64,
  Rc<dyn LrlCallable<(), u64>>>>>>`). LRL has no annotation that erases a data index.
- Not expressible: in-place update (Q11). LRL has no mutable data, and no operation reads or
  writes through a reference (`grep -rn "deref\|Ref Mut\|ref_set\|write_ref\|assign" stdlib/`
  finds nothing; the prelude declares only `borrow_shared` and `borrow_mut`). The reverse of
  Q11 builds new cells (`List::cons(a1, Rc::new(a2))` in the typed backend); the recursor moves
  the tail out of its cell (`lrl_unshare`, which copies the cell only if it is shared) and passes
  a copy of it to the recursive call. Q9's references can therefore only be created and
  passed to functions; the program prints x and y unchanged.
- Macro hygiene (Q8): template binders do not capture user variables (101, not 200), and a local
  binder at the call site does not capture a template's free name; but a global name in a
  template is resolved at the use site (the client's `helper`, 2), and `import-macros` imports
  a file's macros without its definitions, so a library macro cannot refer to a definition of
  its own library (`__lib_only`: `Unbound variable: helper`).
- Code generation: both backends build and run every accepted program (typed and dynamic rows of
  `../results_lrl.md`), including the large elimination of `q01_head.lrl` and the value-indexed
  channels of Q6 and Q7, which the typed backend rejected before the fixes listed below.

## Bugs found while writing these programs (all fixed; no workaround remains)

Each bug had a minimal reproduction `W_D_lrl_compare_<n>.lrl` (kept outside the repository by the
session that found it). The programs used workarounds for bugs 1, 3 and 4; after the fixes they
were removed (implicit arguments are inferred everywhere; the channels of Q5 to Q7 keep a
`List Nat` log) and `../run_lrl.sh` was rerun. Regression tests: `cli/tests/case_study_regressions.rs`.

1. Implicit arguments were not inferred when the expected type has a concrete index and the
   function's result index is a stuck term over the implicits (`(def five (Vec Nat 5) (vappend
   two three))`: F0217 "Cannot unify (rec.Nat ...) with (Nat.succ ...)"). Fixed in the
   elaborator: postponed constraints are retried with every solved metavariable substituted
   (`frontend/src/elaborator.rs`, `unify_core` / `zonk_if_needed`).
2. A `match` whose scrutinee is an application with an implicit argument to infer, e.g.
   `(match (cons 1 nil) Nat ...)`, failed with K0047 "Unresolved metavariable ?0". Fixed
   (`elaborate_match` substitutes solved metavariables in the scrutinee and its type).
3. An application with an implicit argument under a binder in the type of a definition, or in a
   match motive, failed with K0047 "Unresolved metavariable ?0". Fixed (the `Pi` case of the
   elaborator's `infer` and `elaborate_explicit_motive` substitute solved metavariables before the
   kernel types the term).
4. MIR rejected reading a `List Nat` field out of a value of an `affine` inductive in a match
   (M300 / M101 "Copy of non-Copy place"). Fixed: MIR decides Copy-ness of inductive types with
   the kernel's Copy instances (`AdtLayoutRegistry::type_is_copy`, `mir/src/types.rs`).
5. Typed backend: a `Nat` (or `State`) index that is a uniform constructor binder (a value
   parameter of the inductive) was given a `()` constructor argument while call sites passed a
   `u64` (or a `State`): rustc E0308. Fixed in the typed code generator (value parameters keep
   their type).
6. A `Nat` literal of 300 overflowed the compiler's stack (crash, exit status 134). Fixed: the
   CLI runs the compiler on a thread with a large stack (`cli/src/main.rs`); a literal of 1000
   compiles and runs.

Other things that shaped the programs (not bugs):

- A case pattern names only a constructor's explicit fields, so the length of a vector's tail
  (an implicit field of `vcons`) cannot be named. In `send_all` (Q7) the closure's binder type
  is therefore written `(Chan _)`, a hole solved from the motive.
- A curried function whose inner closure owns an earlier non-Copy argument must declare the inner
  binder `#[once]` (e.g. `snoc : (pi l (List A) (pi #[once] x A (List A)))`), otherwise F0206
  "Function kind mismatch: expected Fn, got FnOnce". For the same reason `cong` takes
  `f : (pi #[once] x A B)`, so that it accepts a closure that owns a captured element.
- A `Ref Mut` is not Copy, and passing it to a function moves it (there is no implicit
  reborrow): a first version of `q09_two_mut_refs__alias_live.lrl` that used `r1` twice was
  rejected by the kernel (K0021) instead of by the borrow checker.
- The induction hypothesis is computed before the case body runs, so a print in the `cons`
  case prints the elements last-to-first; the printing helpers (`vprint`, `lprint`) build a
  function of a counter instead, which prints the elements in order.

## Audit note

Observed in the session that wrote these files (2026-10-05), with the CLI binary built from the
working tree (`git describe --always --dirty`: `v0.1.1-2-gefe7bc0-dirty`; SHA-256 prefix in
`../results_lrl.md`) and rustc 1.78.0:

- `LRL_BIN=<that binary> CMP_BUILD_DIR=<tmp> case_studies/comparison/run_lrl.sh` (twice; both
  runs: 83 of 83 cases as expected, about 8 minutes each). Every outcome, diagnostic and output
  quoted above is in `../results_lrl.md` (regenerated after the fixes).
- `../SUMMARY.md` is generated from the three results files by `python3 ../make_summary.py`.
- Verification session (same day, independent rebuild of the CLI, SHA-256 prefix in `../results_lrl.md`):
  `run_lrl.sh` reproduced all 83 cases unchanged; then the `limit` evidence rows for Q9
  (`prelude_ref_ops`, both backends) and Q11 (`rust_dyn_cons` added for the dynamic backend; the
  typed `rust_cons` row became a `limit` row) were added, and the rerun gave 86 of 86 cases as
  expected (`NO_OPERATION_ON_REF` for both Q9 rows, `NOT_IN_PLACE` for both Q11 rows).
- The bugs were reproduced with `lrl run FILE` (bugs 1 to 4, 6) and
  `lrl compile FILE --backend typed -o BIN` (bug 5) on minimal files from the repository root;
  for bug 5 the same file built with `--backend dynamic` printed `Result: Nat(7)`. After the fixes
  the reproductions are accepted (bug 5: typed `Result: 7`; bug 6: `print_nat 1000` runs), and
  `run_lrl.sh` was rerun with the fixed CLI (83 of 83 cases as expected; SHA-256 prefix in
  `../results_lrl.md`).
- The absence of read/write operations on references was checked with the `grep` shown above
  (no match in `stdlib/`) and by reading `stdlib/prelude_api.lrl`.
- That `import-macros` does not import definitions: a client of
  `q08_macro_global_names_lib.lrl` without its own `helper` gives
  `[F0200] ... Unbound variable: helper` (`q08_macro_global_names__lib_only.lrl`).
- That a total `def` may not depend on an axiom: `q04_erasure__forge.lrl` gives `[K0023] ...
  depends on axiom axioms: zero_not_zero. Mark it noncomputable or unsafe`.
