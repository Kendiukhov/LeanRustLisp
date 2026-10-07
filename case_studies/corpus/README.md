# Ownership validation corpus

This directory backs the paper's claim about *where* ownership is enforced in LRL and whether
macros can get around it. For every violation class it holds a small hand-written program
`NN_name.lrl` and a **macro twin** `NN_name_macro.lrl`, in which a macro (`defmacro` with a
quasiquoted template) expands to the same violating code at the call site. For the nearest legal
variants it holds **positive controls** `pNN_name.lrl` (again with macro twins) that must be
accepted and run. (One positive control, P19, keeps the file name `30_proof_closure_duplicated.lrl`
of the violation class it used to be; see "Positive controls".)

All expectations are listed in `manifest.tsv`; `run_corpus.sh` runs everything and writes
`results_corpus.md`; `cli/tests/case_study_corpus.rs` asserts the same expectations in
`cargo test`.

## Running

```sh
# from anywhere; builds the CLI with `cargo build -p cli` unless LRL is set
case_studies/corpus/run_corpus.sh
# or with a given binary, keeping the raw outputs
LRL=/path/to/cli OUT_DIR=/tmp/corpus_out case_studies/corpus/run_corpus.sh
# SKIP_COMPILE=1: positives checked with `run` only; SKIP_TYPED=1: no typed-backend column

cargo test -p cli --test case_study_corpus
```

The script runs `lrl run case_studies/corpus/<file>` with the repository root as working
directory (the CLI finds `stdlib/` relative to it), strips ANSI colours, and takes the code of the
first `Error: [CODE]` line. The stage is derived from the code: `F0104` macro boundary, other
`F01xx` macro expander, `F02xx` elaborator, `K....` kernel, `M...` MIR. Positive controls are also
compiled with `lrl compile <file> --backend dynamic -o <tmp>` and the binary is executed; the
hand-written positives are compiled with `--backend typed` as well (informational column).

The Rust test (`cli/tests/case_study_corpus.rs`) reads the manifest and checks, using the CLI
binary that cargo builds: every listed file exists and every `.lrl` file is listed; every
violation-class file and its twin exit non-zero with the manifest's code and message fragment, and
the twin's code equals the hand-written file's code; the macro-only rows (17, 21) behave as
described below; both versions of every positive control are accepted by `run` and their dynamic
binaries print the expected `Result:` line.

## Manifest columns

`class`, `kind` (`negative`, `macro_only`, `positive`), `file`, `twin`, expected `stage` and
`code` of the hand-written file, a message `fragment` that must occur in its output (for
positives: in the output of its dynamic binary), and the same three columns for the twin, then a
`description`.

## Classes

Most negative programs use an affine token type such as
`(inductive (affine) Tok (sort 1) (ctor mk_tok (pi id Nat Tok)))`, so that the value is not
Copy: the `affine` marker blocks the Copy instance the type would otherwise derive (positive
control P14 shows class 01 accepted without the marker). Classes 03/04 use function values
(function types are not Copy), 12 borrows a `Nat`, 11 uses a state-indexed affine `Door`, 16/31
use `Nat` only, and 18/28 are declarations.

| class | violation | stage, code (both versions) | variant / message |
|---|---|---|---|
| 01 | double use of an affine value | kernel K0021 | `[UseAfterMove]` `t` |
| 02 | use after moving into a function | kernel K0021 | `[UseAfterMove]` `t` |
| 03 | calling a moved function value (read after move) | kernel K0021 | `[UseAfterMove]` `f` |
| 04 | FnOnce closure called twice | kernel K0021 | `[UseAfterMove]` `f` |
| 05 | closure annotated `#[fn]` consumes its capture | elaborator F0207 | `Annotated function kind Fn is too small; requires FnOnce` |
| 06 | repeated (succ) case consumes a captured value | kernel K0021 | `[ConsumedInRepeatedScope]` `k` |
| 07 | recursive field used after its IH consumed it | kernel K0021 | `[RecursiveFieldConsumedByIh]` `rest` |
| 08 | partially applied recursor | kernel K0021 | `[RecursorWithoutMinorPremises]` |
| 09 | fixpoint body consumes a capture | kernel K0021 | `[ConsumedInRepeatedScope]` `k` |
| 10 | implicit non-Copy binder consumed | elaborator F0209 | `Implicit binder of non-Copy type used in consuming position` |
| 11 | operation in the wrong protocol state | elaborator F0214 | `Unification failed: St.closed vs St.opened` (a type error) |
| 12 | two live `&mut` of one value (curried call) | MIR M200 | `already borrowed as Mut` |
| 13 | move while shared-borrowed | MIR M201 | `because it is borrowed as Shared` |
| 14 | reference escapes its referent | MIR M203 | `borrowed value does not live long enough` |
| 15 | reference stored in a constructor; owner moved while the struct is live | MIR M201 | `because it is borrowed as Shared` |
| 16 | total definition calls an `unsafe` definition | kernel K0022 | `EffectError("Total", "Unsafe", "raw_peek")` |
| 17 | axiom injected by a macro (macro-only class) | hand-written: accepted with a warning; twin: macro boundary F0104 | `Axiom 'zero_is_one' declared` / `produced macro boundary form(s): axiom` |
| 18 | `affine` marker with an explicit `copy` request | kernel K0052 | `is marked affine and cannot be Copy` |
| 19 | reference stored in a constructor escapes its referent | MIR M203 | `borrowed value does not live long enough` |
| 20 | two `&mut` of one value stored in two live structs | MIR M200 | `already borrowed as Mut` |
| 21 | `unsafe` definition injected by a macro (macro-only class) | hand-written: accepted; twin: macro boundary F0104 | `produced macro boundary form(s): unsafe` |
| 22 | minor premise does not bind the non-Copy recursive field | kernel K0021 | `[MinorMustBindRecursiveField]` |
| 23 | repeated minor premise given as a let-bound closure | kernel K0021 | `[RepeatedMinorNotLambda]` |
| 24 | leaf case of a branching type returns a non-Copy value | kernel K0021 | `[RepeatedMinorValueNotCopy]` |
| 25 | borrowing a moved value | kernel K0021 | `[UseAfterMove]` `t` |
| 26 | value consumed in one branch, used after the match | kernel K0021 | `[UseAfterMove]` `k` |
| 27 | function type says Fn, closure consumes its capture | elaborator F0206 | `Function kind mismatch: expected Fn, got FnOnce` |
| 28 | `affine` marker on a proposition | kernel K0052 | `is marked affine and cannot be Copy` |
| 29 | value used after a closure captured it by move | kernel K0021 | `[UseAfterMove]` `t` |
| 31 | total definition calls a `partial` definition | kernel K0022 | `EffectError("Total", "Partial", "spin")` |
| 32 | two base cases of a recursive type consume the same captured token | kernel K0021 | `[UseAfterMove]` `t` |

Classes 01–18 are the classes of the evaluation plan (adapted: class 15 is the "owner moved
while the struct holding the borrow is live" form, M201; the "struct returned" form is class 19,
M203; class 16 is the `unsafe` form of the effect violation, class 31 the `partial` form).
Classes 19–32 were added from the verification of the ownership changes: 19/20 are
references stored in data, whose loans MIR now tracks (regression tests in
`cli/tests/loans_proofs_switch_regressions.rs`), 22–24 are the remaining recursor rules of the
kernel walk (`docs/diagnostic_codes.md`, K0021 variants), 25/26/29 are further use-after-move
shapes (borrow, branch, capture), 27 is the type-annotation form of class 05, 28 is the `affine`
marker on a proposition, and 32 shows that the
cases of a match on a RECURSIVE type are not alternatives: its minor premises are all evaluated
before the dispatch (`docs/spec/mir/index.md`, "Recursor Lowering and Its Limits"), so two base cases may not
both consume the same value (compare P01 for a non-recursive type).

### Which component rejects what

* **Kernel (trusted)**: every K0021 class (01–04, 06–09, 22–26, 29, 32), the effect classes 16
  and 31 (K0022) and the marker classes 18/28 (K0052). The kernel's ownership walk counts a borrow as a
  read (or mutable use) of the borrowed variable; it does **no loan tracking**.
* **MIR (untrusted)**: loan conflicts and lifetimes — classes 12, 13, 14, 15, 19, 20
  (M200/M201/M203). These are rejected only by MIR's NLL borrow check: the kernel accepts these
  programs by design (`docs/spec/kernel_boundary.md`: the kernel "does **not** check borrows
  against each other ... that is the MIR borrow checker's job, outside the TCB").
* **Elaborator (untrusted)**: kind annotations and implicit binders (05, 10, 27) and the protocol
  type error (11) are reported by the elaborator, before the kernel sees the definition. The
  kernel has its own checks for the first group (`K0043` FunctionKindTooSmall and the
  `ImplicitNonCopyUse` variant of `K0021`, `docs/diagnostic_codes.md`); whether they would fire
  without the elaborator is not measured here (that is the stage matrix's job).
* **Macro expander**: classes 17 and 21 are macro-only. User code may declare axioms and `unsafe`
  definitions directly (the hand-written files are accepted; the axiom is reported as a warning and
  tracked), but a macro expansion that produces `axiom`, an `unsafe` definition, `eval` or
  `(import classical)` is rejected at the call site with F0104 (`--macro-boundary-warn` turns this
  into a warning; the list of forms is the one of `docs/spec/macro_system.md` and
  `collect_macro_boundary_hits_in_list` in `frontend/src/macro_expander.rs` — this corpus
  exercises `axiom` and `unsafe`). Variants tried during construction were also rejected with F0104: the `axiom`
  head passed to a macro as an argument, an axiom produced by a nested macro, and an axiom produced
  by a macro used inside a `def` body.
* **Former class 30, now positive control P19**: an FnOnce closure whose type
  `(pi #[once] u Nat Tru)` is a proposition, passed twice. Such a closure is a proof: erased at run
  time and therefore Copy (`docs/spec/ownership_model.md`), so duplicating it is legal, and the
  kernel accepts it. MIR used to lower the closure as a value that captured (moved) the token and
  reported M100 for the second use, a false positive of MIR. MIR lowering now builds proof-typed
  closures without captures and never evaluates proof-valued terms (`mir/src/lower.rs`, the
  `Term::Lam` case and `is_erased_proof_function_destination`), so the program is accepted by every
  stage and runs.

### Macro twins

Every twin of a violation class produced the same first diagnostic code as its hand-written
version (see `results_corpus.md`). Twins reuse the hand-written program and replace the violating
expression by a macro call; templates introduce their own binders (`let`, `lam`, `fix`, pattern
variables), which are hygienic. The twins' diagnostics carry a macro label ("macro 'm' expanded
here" when the macro call lies inside the reported span, "in code produced by macro 'm'" when the
reported span lies inside the call, "macro expansion: m" for F0104), except class 15 (the M201
is reported at `(burn t)`, outside the macro call). (Classes 10 and 11 had no label in the first
run of the corpus because their F0209 / F0214 diagnostics had no source span; both now have one.)

### Positive controls

| class | nearest legal variant of | program |
|---|---|---|
| P01 | 01, 26 | the same token consumed in both branches of a match on Bool |
| P02 | 13 | shared borrow dead before the move (non-lexical lifetimes) |
| P03 | 12 | two live shared borrows |
| P04 | 04, 05 | Fn closure that borrows its capture, called twice; capture moved afterwards |
| P05 | 06 | the base case of a linear recursion consumes a captured token once |
| P06 | 03 | function value called before it is moved |
| P07 | 04 | FnOnce closure consuming a token called once |
| P08 | 11 | protocol operations in the right order |
| P09 | 12, 20 | two `&mut` borrows that are not live at the same time, then a move |
| P10 | 02 | a value mentioned inside a proof is not moved by it |
| P11 | 15 | struct holding a borrow is dead before the owner is moved |
| P12 | 06 | the repeated case calls (reads) a captured Fn function |
| P13 | — | an affine token dropped unused (documents what is not enforced) |
| P14 | 01 | class 01 without the `affine` marker (Copy is derived) |
| P15 | 01 | hygiene: the macro's own `t` and the caller's `t` are different variables |
| P16 | 07 | a Copy recursive field (`List Nat`) used together with its IH |
| P17 | 10 | an implicit non-Copy binder borrowed (read), not consumed |
| P18 | 09 | a fixpoint body calls (reads) a captured Fn function |
| P19 | (former 30) | an FnOnce closure whose result is a proof, passed twice (file `30_proof_closure_duplicated.lrl`) |

## What is not enforced

* **Affine, not linear.** A non-Copy value may be dropped without being used (P13: accepted by
  every stage, the binary prints `Result: Nat(0)`). In particular an unclosed channel is accepted.
  The error `LinearNotConsumed` (M104) is defined in `mir/src/errors.rs` but never constructed;
  `docs/spec/ownership_model.md` used to list "Linear type consumption ... exactly once" among
  MIR's checks and now says that values are affine and that M104 is never reported.
* **Global definitions are constants.** A top-level `(def g Tok (mk_tok 1))` of an affine type
  may be referenced more than once (each reference denotes the definition's value anew; checked
  in this session with a separate probe, not part of the corpus; documented in
  `docs/spec/ownership_model.md` §1.2).

## Findings and workarounds

Found while building the corpus (minimal reproductions are kept outside the repository with the
case-study reports; none of them affects which programs are accepted or rejected). Items 1 to 3
and 5 have since been fixed in the compiler (regression tests in
`cli/tests/case_study_regressions.rs`); item 4 remains.

1. *(fixed)* `F0209` (class 10) had no source span and named the variable by its de Bruijn index
   (`... in consuming position at de Bruijn index 0`); `F0214` (class 11) had no source span
   either, so the class-10 and class-11 twins had no macro label. Now F0209 reads `... in consuming
   position: variable 't'` with the span of the lambda, F0214 has the span of the checked
   argument, and both twins carry the macro label.
2. *(fixed)* For a quasiquoted template, `F0104` named the built-in `quasiquote` instead of the
   user macro in its headline, and each boundary violation was reported as two `F0104` errors.
   Now one `F0104` names the user macro (`Macro expansion for 'postulate' produced macro boundary
   form(s): axiom`).
3. *(fixed)* Macro parameters were substituted for every occurrence of their name in the
   template, also inside a quasiquote where they are not unquoted; a parameter named `ctor`
   replaced the keyword `ctor` in the twin of class 18 (`F0102`), whose parameter was therefore
   named `c`. Now only unquoted occurrences are replaced inside a quasiquote
   (`docs/spec/macro_system.md`), and the twin of class 18 names its parameter `ctor` again.
4. *(open)* `--expand-full` prints macro-introduced binders without their hygiene scopes: the
   printed expansion of `p15_hygienic_binder_macro.lrl` is
   `(lam t Tok (let t Tok (mk_tok 1) (add (burn t) (burn t))))`, which as a program is rejected
   (K0021), whereas the macro program is accepted and prints `Result: Nat(5)`. P15's hand-written
   version is therefore the alpha-renamed expansion (`t2`), not the printed one.
5. *(fixed, documentation)* see "Affine, not linear" above (M104).

The only workaround left in the corpus is the alpha-renamed P15 (item 4).

## Results

See `results_corpus.md` (generated by `run_corpus.sh`). In the first recorded run, all 50 manifest
rows (30 violation classes with a hand-written version and a twin, 2 macro-only classes, 18
positive controls; 100 programs) matched their expectation, and every macro twin of a violation
class produced the same first diagnostic code as its hand-written version. The run was repeated
after the compiler fixes listed under "Findings": again 50 of 50 rows, and every twin of a
violation class except class 15 carries a macro label. After MIR lowering stopped evaluating
proof-typed closures, former class 30 became positive control P19; in the current recorded run
(CLI sha256 in `results_corpus.md`) all 50 rows (29 violation classes, 2 macro-only classes, 19
positive controls; 100 programs) match, every twin of a violation class has the same first code
as its hand-written version, and all 19 hand-written positive controls also compiled and ran
under the typed backend (informational column).

## Audit note

Facts in this README were verified in the session that built the corpus (2026-10-05), with the CLI
binary built from the working tree at that time:

* Every code, variant and message fragment above was observed with `lrl run <file>` (cwd =
  repository root, ANSI stripped) and is checked by `run_corpus.sh` and
  `cli/tests/case_study_corpus.rs`; positive results with `lrl compile <file> --backend dynamic
  -o <tmp>` and running the binary.
* Counts: `grep -c . manifest.tsv` minus the comment lines and the header gives the 50 rows (after
  the P19 change: `grep -c . manifest.tsv` = 54, four comment/header lines; by kind 29 `negative`,
  2 `macro_only`, 19 `positive`, counted with `awk -F'\t'` over the `kind` column; 19 `built:`
  entries in the typed column of `results_corpus.md`);
  `ls case_studies/corpus/*.lrl | wc -l` gave 100; the "50 of 50" result is the summary line that
  `run_corpus.sh` wrote into `results_corpus.md`; `cargo test -p cli --test case_study_corpus`
  passed (3 tests). A mutation check (row 01 expecting `K0022`, P01 expecting `Result: Nat(99)`)
  made two of the three tests fail with exactly those rows, then the manifest was restored.
* F0104 variants: probes with the `axiom` head passed as a macro argument, a nested macro, and a
  macro inside a `def` body, each run with `lrl run` (all `F0104`); `--macro-boundary-warn`
  turned the class-17 twin into exit status 0 with `Warning: [F0104] ...`.
* `LinearNotConsumed`: `grep -rn LinearNotConsumed kernel frontend mir codegen cli` returns only
  `mir/src/errors.rs` (definition, display and code mapping).
* `--expand-full` output: `lrl --expand-full case_studies/corpus/p15_hygienic_binder_macro.lrl`;
  the printed definition, run as a separate file, gave `K0021 [UseAfterMove]: variable 't'`.
* Macro parameter substitution: `lrl --expand-full` on the class-18 twin with the parameter named
  `ctor` printed `(inductive copy (affine) Chan (sort 1) (mk_chan mk_chan (pi id Nat Chan)))`;
  the substitution code is `substitute_rec_with_scope` in `frontend/src/macro_expander.rs`.
* Global affine definition referenced twice: a probe with `(def g Tok (mk_tok 1))` and
  `(mk_tp g g)` exited 0 and its dynamic binary printed `Result: Nat(2)`.
