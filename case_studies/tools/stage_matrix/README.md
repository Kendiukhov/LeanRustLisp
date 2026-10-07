# Stage matrix

`stage_matrix` reports, for every top-level definition of an LRL file (`def`, `partial`, `unsafe`,
`noncomputable`, including definitions whose body calls a macro) and for every top-level
expression, the verdict of **each compiler stage separately**:

| field | stage | how it is computed |
|---|---|---|
| `elab` | frontend | the driver's pre-checks (reserved name, frozen-prelude redefinition, `fix` outside `partial`), `Elaborator::infer_type` / `check` (or `infer` for an expression), constraint solving, `validate_core_term` |
| `kernel_typing` | kernel typing | `kernel::checker::infer` + `whnf` on the type, `kernel::checker::check` on the value (the driver's "Kernel re-check") |
| `kernel_admit` | kernel admission | `Env::add_definition` on a **clone** of the environment: typing, the kernel ownership walk, capture-mode validation, effects, termination, axiom dependencies; `phase` says which of these failed |
| `kernel_ownership` | kernel ownership walk | derived from `kernel_admit`: `reject` (K0021), `pass` (admitted, or failed in a phase after the walk), `not_reached` (failed in typing) |
| `mir` | MIR | lowering of the elaborated term, then MIR typing (`TypingChecker`), MIR ownership (`OwnershipAnalysis`, moves) and the NLL borrow checker (`NllChecker`) on the definition body **and every derived closure body** — the same sequence as `validate_definition_mir` in `cli/src/driver.rs` (without the `--panic-free` lints) |
| `cli` | the real CLI | the form replayed through the unmodified `cli::driver::process_code` |

The MIR part is computed **even when the kernel rejects** the definition: the elaborated term is
lowered in the environment before admission (`mir.env = "pre_admission"`) with the capture modes
computed by the elaborator. When the kernel admits the definition, MIR is run on the admitted
definition exactly as the CLI does (`mir.env = "admitted"`). No compiler API is changed or weakened:
the tool only reads the environment it is given and calls public functions of the `cli`, `kernel`,
`frontend` and `mir` crates.

## Build and run

```bash
# from the repository root
case_studies/tools/run_stage_matrix.sh            # build, run every set, write ../results_stage_matrix.md

# one file (JSON lines on stdout); --backend typed loads the typed prelude stack used by `compile`
(cd case_studies/tools/stage_matrix && cargo build)
case_studies/tools/stage_matrix/target/debug/stage_matrix [--backend dynamic|typed] [--allow-axioms] \
    [--macro-boundary-warn] [--allow-redefine] [--dump-mir NAME|all] path/to/file.lrl
```

Run it from the repository root: like the CLI, it finds `stdlib/` relative to the working
directory. `--dump-mir NAME` prints the MIR of definition `NAME` (and of its closures) to stderr.
`run_stage_matrix.sh` honours `STAGE_MATRIX_TARGET_DIR`, `STAGE_MATRIX_BACKENDS` (default
`dynamic typed`), `STAGE_MATRIX_JOBS`, `STAGE_MATRIX_TIMEOUT` and `STAGE_MATRIX_OUT` (default
`case_studies/tools/stage_matrix_results/`, one `<backend>/<set>.jsonl` per file set) and
`STAGE_MATRIX_CLI`.

Sets: `corpus` = `case_studies/corpus/`, `case_studies` = `case_studies/lrl/` (including `neg/` and
`limits/`), `tests` = `tests/`, `code_examples` = `code_examples/`, `mir_gaps` =
`case_studies/tools/stage_matrix/gaps/` (minimal programs, see below); `packages/` fixtures are
excluded (they need the package manager; `cli/tests/lrl_corpus_expectations.rs` skips them for the
same reason). Missing directories are skipped. `tests/backend_conformance/cases/` are written for
their own prelude (`tests/backend_conformance/conformance_prelude.inc`), so some of them are
rejected under the standard prelude; the results file marks them.

Optional: with `STAGE_MATRIX_CLI=<path to a CLI binary built from the same tree>`, the script also
runs every file of the dynamic run as `<cli> run <file>` and compares the diagnostic codes of its
`Error:` lines and its exit status with the per-form replay (`check_against_cli.py`).

Provenance: the header of `results_stage_matrix.md` records the repository commit (`git rev-parse
--short HEAD`, with a note if tracked files have uncommitted changes) and the SHA-256 of the
`stage_matrix` tool binary that produced the JSON lines and of the `STAGE_MATRIX_CLI` binary used
for the cross-check; `run_stage_matrix.sh` computes both (`shasum -a 256`, or `sha256sum`) and passes
them to `summarize.py` (`--tool-sha256`, `--cli-sha256`).

## Method

1. The prelude is loaded as `lrl run` loads it (`package_manager::load_prelude`: dynamic stack,
   `init_marker_registry`) or, with `--backend typed`, with the typed stack used by `compile`.
2. The file is parsed, and every top-level form is expanded into a declaration **before any
   declaration is processed**, with one `DeclarationParser` — as `process_code_inner` does. A parse
   or expansion error rejects the whole file (record `file` with `status` `parse_error` /
   `expansion_error`), as in the CLI.
3. Forms are then processed in order. For a definition or expression, all stages above are
   computed against the current environment. Then the form is **replayed** through
   `cli::driver::process_code` on the real environment, with the source text of every other form
   replaced by spaces (newlines kept, so spans and line numbers are unchanged). The replay advances
   the environment exactly as the CLI would (a rejected definition is not added, so later
   definitions that use it fail elaboration, as in the CLI) and gives the CLI's own verdict.
4. **Self-check**: for every definition the tool predicts admission (`kernel_admit` ok, the
   driver's interior-mutability gate C0005 not triggered, every MIR check ok) and compares it with
   the replay (`consistent`). `results_stage_matrix.md` reports the number of inconsistent records;
   any non-zero count means the harness does not mirror the pipeline and its rows must not be used.

Output records (`record` field): `file` (status), `def` (one per definition / expression),
`form` (other declarations: inductive, axiom, instance, defmacro, module/import/open; replay verdict
only), `end` (counts), and `crash` (added by `run_matrix.py` when a run exits abnormally). `def`
records also carry `macros_called` (file-local macros called in the form, found syntactically) and
the replay's diagnostics with their labels (e.g. `macro 'm' expanded here`).

## Known differences from the CLI (deliberate, documented)

* Top-level expressions are checked like `check_expression_admission` (an anonymous `unsafe`
  definition on a scratch environment) but **not evaluated** (`show_eval` is off), so the
  evaluation gate `C0004` (axiom-dependent expression) is not reproduced.
* The work runs on a thread with a 256 MiB stack (the CLI runs the compiler on a thread with a
  1 GiB stack, `COMPILER_STACK_SIZE` in `cli/src/main.rs`), so that one very deep term does not
  abort the remaining records of a file; panics inside a stage are caught and recorded (`panic`)
  instead of aborting.
* The panic-free lints (`--panic-free`) are not run.
* The kernel ownership walk (`check_ownership_in_term`) is private; its verdict is derived from the
  phase in which `Env::add_definition` failed. When kernel typing fails the walk is not reached.
* When kernel typing fails, the MIR result is computed on an ill-typed term; it is reported but
  should not be read as a verdict (the summary only draws conclusions from definitions that pass
  kernel typing or are rejected earlier).
* The replay re-expands the replayed form after all `defmacro` forms of the file are registered,
  whereas the CLI expanded it with only the earlier ones registered; the stage analysis itself
  uses the CLI-order expansion. The self-check detects any resulting difference in verdicts.

## Findings recorded in `../results_stage_matrix.md`

The results file is generated; the cause notes it prints for divergent definitions come from
`CAUSE_NOTES` / `KERNEL_ONLY_NOTES` in `summarize.py` and were established by reading the MIR
(`--dump-mir`) and the cited sources. When MIR runs on the same elaborated term, it did **not**
reject the following kernel-rejected (K0021) programs when the probes were written, i.e. MIR was not
an independent second line of defence for them; (a), (b), (d) and (e) have been fixed since, (c)
remains. Each mechanism has a minimal program in `gaps/` (set
`mir_gaps`); the results file recomputes on every run whether each probe still diverges:

| | mechanism (MIR side) | corpus class | minimal program |
|---|---|---|---|
| (a) | `check_operand_moves` (`mir/src/analysis/ownership.rs`) did not mark a moved local of Fn/FnMut function type as moved (comment: "Function values are duplicable in the source semantics"). **Fixed after this tool was written**: a move of a function value by assignment, argument or switch operand marks it moved; inside the capture list of a closure literal it does not (lowering moves function values that the closure only calls into its environment, a read for the kernel) | 03 | `gaps/g2_moved_fn_value_called.lrl` |
| (b) | `check_rvalue_structured` checked only `Rvalue::Use`; a borrow `&_2` of a moved local was not checked, and NLL tracks loans, not moves. **Fixed after this tool was written**: `Rvalue::Ref` and `Rvalue::Discriminant` places are checked like reads | 25 | `gaps/g1_borrow_after_move.lrl` |
| (c) | a fixpoint body reads its captures with `copy _1.k` from an environment local typed `()` and marked Copy. **Open**: MIR does not re-check closure kinds (whether a body that may run many times consumes a capture); the elaborator (F0206/F0207) and the kernel (K0043, `ConsumedInRepeatedScope`) do. The same holds for `Fn` closures (corpus class 05 is elaborator-only) | 09 | `gaps/g3_fix_consumes_capture.lrl` |
| (d) | a recursive-case arm that does not use its non-Copy recursive field passed the whole major premise and the minor-premise closure once to the recursor entry function, which calls the closure once per constructor outside MIR. **Fixed while this tool was written**: entry dispatch now requires the minor-premise local to be Copy (`mir/src/lower.rs`, `local_is_copy` before `rec_arm_dispatches_to_entry`); the probe stays as a regression test | (06 on a non-Copy type) | `gaps/g4_dispatched_minor_consumes_capture.lrl` |
| (e) | `mir/src/lower.rs` marked a closure's destination local Copy when that closure's captures were all Copy; a capture-free closure written in one branch made the local that holds an FnOnce closure from the other branch Copy. **Fixed after this tool was written**: a local is Copy only if every closure written into it has only Copy captures (`non_copy_closure_locals` / `copy_closure_locals`) | - | `gaps/g5_copy_marked_fnonce_local.lrl` |

The kernel rejects all of them, so the full pipeline rejects them; the gaps matter only for the
claim that MIR independently re-checks ownership. Effects (K0022) and axiom dependencies (K0023)
are kernel-only checks by design. In the other direction (kernel accepts, MIR rejects; the program
is rejected): loan errors (M200/M201/M203, the kernel has no loan tracking), and an `FnMut` closure that
reborrows a captured `&mut` inside a repeatable minor premise (`gaps/g7_fnmut_minor_reborrow.lrl`: the
minor-premise closure holds a `&mut`, is not Copy and is used twice, M100; and a reborrow through a captured
reference returned by a closure, M203). A closure whose result is a proof, duplicated (former corpus class
30, now positive control P19), used to be rejected by MIR (M100); proof-typed closures are now built
without captures (`docs/spec/mir/index.md`, "Proofs in Lowering"). `gaps/g6_large_elim_variable_index.lrl` is a regression
probe for a former divergence of this direction (MIR typing M300 on a type computed by large
elimination at a variable index; MIR accepts it since stuck types are compatible with loan-free
known types, `stuck_type_meets_loan_free_type` in `mir/src/analysis/typing.rs`).

## Audit note (CLAUDE.md no-fabrication rule)

Written on 2026-10-05. Verified in that session:
* Identifiers and paths cited above were read in, or found with `grep -n` in, the files named next to
  them: `process_code_inner`, `validate_definition_mir`, `check_expression_admission`,
  `build_term_span_map`, `uses_interior_mutability_axioms`, code `C0005` (`cli/src/driver.rs`);
  `load_prelude` (`cli/src/package_manager.rs`); `prelude_stack_for_backend` (`cli/src/compiler.rs`);
  `Env::add_definition`, `check_ownership_in_term` (private), `TypeError::diagnostic_code`
  (`kernel/src/checker.rs`); `check_operand_moves`, `check_rvalue_structured`
  (`mir/src/analysis/ownership.rs`); the `decl.is_copy = true` closure rule and the `local_is_copy`
  condition before `rec_arm_dispatches_to_entry` (`mir/src/lower.rs`);
  `stuck_type_meets_loan_free_type` (`mir/src/analysis/typing.rs`); `conformance_prelude.inc`
  (`ls tests/backend_conformance/`); the `packages` exclusion (`cli/tests/lrl_corpus_expectations.rs`).
* The mechanisms (a)-(e) were established from `stage_matrix --dump-mir <def> <file>` on the `gaps/`
  programs and the corpus classes 03, 09, 25 (e.g. `_6 = move _2` followed by the call `&_2(...)`;
  `_5 = move _2; ...; _7 = &_2`; `_3 = copy _1.1` with `_1: () (env) [copy]`; one move of the minor
  closure into `recursor TL`; `_4: fn_once(Nat) -> Nat [copy]` called twice).
* The self-check (count of inconsistent records) and the CLI cross-check (`check_against_cli.py`) are
  computed by the script on every run and printed in `../results_stage_matrix.md`; no number in this
  README is asserted beyond those runs.
* After the fixes of mechanisms (a), (b) and (e) (`check_operand_moves_in`, the `Rvalue::Ref` /
  `Rvalue::Discriminant` case of `check_rvalue_structured` in `mir/src/analysis/ownership.rs`;
  `non_copy_closure_locals` / `copy_closure_locals` in `mir/src/lower.rs`), the script was rerun
  (`STAGE_MATRIX_JOBS=5 STAGE_MATRIX_CLI=<cli> case_studies/tools/run_stage_matrix.sh`); in that run's
  results file the probes g1, g2, g4, g5, g6 show `diverges = no`, g3 shows `yes`, and corpus classes
  03 and 25 move to "kernel and MIR both reject".
* Later on 2026-10-05, after MIR lowering stopped evaluating proof-typed closures (former corpus class
  30, now positive control P19) and after the two lowering fixes for nested captures of mutable
  references (re-borrowing through a borrowed capture; closure bodies continue the enclosing region
  counter, `next_region` in `mir/src/lower.rs`), `gaps/g7_fnmut_minor_reborrow.lrl` was added and the
  script was rerun (`STAGE_MATRIX_JOBS=5 STAGE_MATRIX_CLI=<cli> case_studies/tools/run_stage_matrix.sh`):
  0 crash records in all 10 backend x set combinations, CLI cross-check 329 of 329 identical; the
  results file lists P19 among the positive controls (every stage passes), the "MIR only (kernel
  accepts)" bucket has 6 classes (12, 13, 14, 15, 19, 20), and g7 shows `diverges = yes` (kernel
  accepts; MIR rejects with M100 and M203, the mechanisms named in its cause note, established from
  `stage_matrix --dump-mir f` on the program).
