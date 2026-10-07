# Paper examples

Every LRL code example printed in the paper (`paper/jot_r1/`) that is not part of a case-study
file is a separate program here. `manifest.tsv` records what the compiler must do with each file
(accept it, or reject it with a given diagnostic code) and a message fragment;
`cli/tests/paper_examples.rs` checks every row with the real CLI in `cargo test`:

```sh
cargo test -p cli --test paper_examples
```

For a rejected file the test runs `cli run case_studies/paper_examples/<file>` from the repository
root and checks the exit status, the code of the first `Error: [CODE]` line and the fragment. For
an accepted file it checks that `cli run` succeeds without an error, builds the program with
`cli compile <file> --backend dynamic -o <tmp>`, runs the binary and checks that it prints the
fragment. It also checks that every `.lrl` file of this directory is listed exactly once.

Where a paper example is a definition without an entry point, the accepted file adds a `main`
that applies it, so that its behaviour is observable; the `main` is not printed in the paper (the
file's header comment says so). Every other line of the printed example is reproduced as printed.

## Files

Paper locations are given by subsection title and LaTeX label (`paper/jot_r1/sections/`).

| file | paper | what the paper says | expected |
|---|---|---|---|
| `pair_with.lrl` | "Function kinds" (`sec:core:kinds`, `core.tex`) | in a curried function each Π has its own kind: the inner function moves the captured token, so it is `#[once]`; the outer one is `Fn` | accepted; binary prints `Result: Nat(1)` |
| `pair_with_inner_pi_unannotated.lrl` | same | "Without the annotation `#[once]` on the inner Π the elaborator rejects the definition (F0206)" | `F0206` `Function kind mismatch: expected Fn, got FnOnce` |
| `pair_with_inner_pi_fn.lrl` | same | the same with the inner Π annotated `#[fn]` | `F0206` (same message) |
| `spend_succ.lrl` | "Where kinds meet dependent elimination" (`sec:own:rec`, `ownership.tex`) | the succ case runs n times and consumes the captured token each time | `K0021` `[ConsumedInRepeatedScope]: non-Copy variable 'k' ...` |
| `spend_zero.lrl` | same | "Consuming `k` in the `zero` case instead is accepted, because that case runs once" | accepted; binary prints `Result: Cons(Tok, Nil)` |
| `with_zero_macro.lrl` | "Hygiene" (`sec:macros:hygiene`) and "The phase barrier" (`sec:macros:barrier`), `macros.tex` | with `(defmacro with-zero (e) (let x Nat zero e))`, `(lam x Nat (with-zero x))` returns the caller's `x`, not zero | accepted; applied to 3, binary prints `Result: Nat(3)` |
| `with_zero_by_hand.lrl` | "The phase barrier" (`sec:macros:barrier`) | the expansion's text `(lam x Nat (let x Nat zero x))`, written by hand, returns zero | accepted; binary prints `Result: Nat(0)` |
| `widen_fnmut_reborrow.lrl` | "What is proved" (`sec:own:meta`, `ownership.tex`), after Lemma "Kind widening" | the compiler accepts an FnMut closure that reborrows a captured mutable reference ... | accepted; binary prints `Result: Nat(2)` |
| `widen_fnonce_moves.lrl` | same | ... and rejects the same closure annotated FnOnce when the reference is used afterwards (K0021) | `K0021` `[UseAfterMove]: variable 'r' is used after it was moved` |
| `read_after_move_through_closure.lrl` | "Who enforces what" (`sec:own:trust`) and "What is proved" (`sec:own:meta`), `ownership.tex` | reading a value through a reference held by a closure, after the value was moved, is a borrow conflict rejected by MIR (M201) | `M201` `... because it is borrowed as Shared` |
| `minor_reads_scrutinee_moves.lrl` | "What is proved" (`sec:own:meta`, `ownership.tex`), paragraph "The mechanized core calculus" | O-Rec-Seq checks the minor premises before the scrutinee, so the kernel accepts a recursor application whose minor premise reads a resource that the scrutinee consumes (here the `succ` case reads the token `t` through `(peek (& t))` while the scrutinee is `(burn t)`), and MIR rejects it as a use of a value while it is borrowed (M201) | `M201` `... because it is borrowed as Shared` |

The examples of "LRL by Example" (`sec:tour`, `tour.tex`) are not repeated here: every top-level
form printed there (`Vec`, `Chan`, `close`, `defsend`, `log`, the two `defsend` calls, `send_all`,
`vreverse_involutive`) occurs in `case_studies/lrl/protocol.lrl` or `case_studies/lrl/vectors.lrl`
(see the audit note), which `cli/tests/case_studies.rs` runs; the appendix listings are those two
files. The inline fragments of the paper that are schemas rather than programs (for example
`(def name Type value)` or `(match e (motive M) ...)`) are not programs and have no file.

## Audit note

Checked on 2026-10-05 with the CLI built from the working tree of that day (cwd = repository root,
ANSI colours stripped):

* Each expected outcome, code and fragment in `manifest.tsv` was observed with
  `cli run case_studies/paper_examples/<file>` and, for accepted files, with
  `cli compile <file> --backend dynamic -o <tmp>` followed by running the binary;
  `cargo test -p cli --test paper_examples` passed (2 tests). A mutation of the manifest
  (`spend_succ.lrl` expecting `F0206`, `with_zero_macro.lrl` expecting `Result: Nat(0)`) made
  `paper_examples_behave_as_the_paper_states` fail with exactly those two rows; the manifest was then
  restored.
* The printed examples were copied from `paper/jot_r1/sections/core.tex` (the `pair_with` listing),
  `ownership.tex` (the `spend` listing and the prose about widening and M201) and `macros.tex` (the
  `with-zero` example). A script extracted the `lstlisting` blocks of `core.tex` and
  `ownership.tex` and found each of the two listings verbatim in `pair_with.lrl` and
  `spend_succ.lrl`. The widening and read-after-move programs are the probes that were used to
  check that prose.
* "Every top-level form of the tour occurs in the case-study files": a script extracted the
  `lstlisting` blocks of `tour.tex`, split them into top-level forms, removed comments, normalised
  whitespace and searched each form in `case_studies/lrl/protocol.lrl` and
  `case_studies/lrl/vectors.lrl`: all were found (`Vec` in both, `send_all` and the channel forms in
  `protocol.lrl`, `vreverse_involutive` in `vectors.lrl`).
* `minor_reads_scrutinee_moves.lrl` (added 2026-10-06) is the probe that was used to check the
  sentence of `sec:own:meta` about the kernel accepting a minor premise that reads a resource the
  scrutinee consumes. Before adding it, `cli run` on the same program printed, as its first error,
  `[M201] Borrow error in f closure 3: cannot use Place { local: Local(2), projection: [] } because
  it is borrowed as Shared` (no `K` diagnostic), with the CLI built from the working tree of
  2026-10-06; the manifest row was then checked by `cargo test -p cli --test paper_examples`.
