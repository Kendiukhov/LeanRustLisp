# Test Plan: Mode A - Semantics & IR Stability

**Author:** Test Engineer Agent  
**Date:** 2026-02-01  
**Mode:** Pre-Codegen / Pre-Typed-Backend  
**Purpose:** Lock down semantics and IR artifacts so later changes cannot silently shift meaning.

---

## 1. Current State (Implemented)

**Kernel**
- `kernel/tests/semantic_tests.rs`: impredicative Prop, defeq beta/delta/zeta/iota, transparency, substitution, inductives.
- `kernel/tests/negative_tests.rs`: must-fail cases for type errors, universes, Prop elimination, inductive soundness.
- `kernel/tests/fuzz_no_panic.rs`: bounded no-panic corpus for type checking.

**Frontend**
- `frontend/tests/macro_expansion_tests.rs`: macro determinism + hygiene snapshots.
- `frontend/tests/elaboration_tests.rs`: stable core term snapshots + determinism.
- `frontend/tests/golden_expansion.rs`: file-driven macro expansion snapshots from `cli/tests/golden/frontend`.
- `frontend/tests/fuzz_no_panic.rs`: bounded parser/expander fuzz corpus.

**MIR & Borrowing**
- `mir/src/analysis/nll_tests.rs`: NLL accept/reject unit tests.
- `mir/tests/borrowck_corpus.rs`: extended NLL corpus (branches, reborrows, loops).
- `mir/src/lints.rs`: panic-free profile lints (RefCell flagged, Mutex allowed).

**CLI / Pipeline**
- `cli/tests/golden_suite.rs`: file-driven golden pipeline snapshots (elab + MIR + borrowck).
- `cli/tests/pipeline_golden.rs`: unified pipeline determinism snapshot.
- `cli/tests/pipeline_negative.rs`: parse/type diagnostic snapshots.
- `cli/tests/pending_borrow_surface.rs`: ignored placeholder for future surface borrow syntax.

---

## 2. Golden Semantics Suite Layout

```
cli/tests/golden/
├── kernel/    # core semantics (defeq, inductives, lists)
├── frontend/  # macro expansion + hygiene edge cases
├── mir/       # MIR lowering stability
└── negative/  # must-fail parse/type diagnostics
```

Snapshots live in `cli/tests/snapshots/` and `frontend/tests/snapshots/`.

---

## 3. Decision Coverage Matrix

| Decision | Test File(s) | Notes |
|----------|--------------|-------|
| Impredicative Prop | `kernel/tests/semantic_tests.rs` | `test_impredicative_prop_basic` + variants |
| Prop elimination restriction | `kernel/tests/negative_tests.rs`, `kernel/tests/semantic_tests.rs`, `frontend/tests/elaboration_tests.rs` | `negative_large_elim_from_prop`, `negative_large_elim_multiple_ctors`, `test_prop_elimination_restricted`, `elaboration_prop_elim_rejected` |
| Allowed large elim (singleton Prop) | `kernel/tests/semantic_tests.rs` | `test_large_elim_allowed_for_prop_singleton` |
| Transparent default | `kernel/tests/semantic_tests.rs` | `test_transparent_unfolds_in_defeq` |
| Opaque escape hatch | `kernel/tests/semantic_tests.rs` | `test_opaque_does_not_unfold` |
| Classical axiom tracking | `kernel/tests/semantic_tests.rs`, `cli/tests/pipeline_golden.rs` | `test_classical_axiom_tracking`, `golden_pipeline_classical_axiom_tracking` |
| Defeq determinism | `kernel/tests/semantic_tests.rs` | `test_defeq_deterministic` |
| NLL acceptance | `mir/tests/borrowck_corpus.rs` | multi-case corpus |
| NLL rejection | `mir/tests/borrowck_corpus.rs` + `mir/src/analysis/nll_tests.rs` | explicit rejects |
| Panic-free profile lint | `mir/src/lints.rs` | `test_rejects_refcell` |
| Macro determinism/hygiene | `frontend/tests/macro_expansion_tests.rs` | snapshot-based |
| Match exhaustiveness + duplicate cases | `frontend/tests/elaboration_tests.rs` | `elaboration_match_missing_case_rejected`, `elaboration_match_duplicate_case_rejected` |

---

## 4. Determinism Checks

- `cli/tests/golden_suite.rs`: double-run per fixture, exact output match.
- `frontend/tests/elaboration_tests.rs`: repeated elaboration equality.
- `frontend/tests/macro_expansion_tests.rs`: repeated expansion equality.

---

## 5. Known Gaps / TODO

- Surface borrow syntax: keep `tests/pending/borrow_surface.lrl` and enable once parser supports refs.
- Classical dependency metadata is now exposed via pipeline artifacts; extend to REPL commands if needed.
- CI workflow file not committed yet; recommended to run `cargo test --all` + snapshot checks.

---

## 6. Maintenance Notes

- Update snapshots with `INSTA_UPDATE=always cargo test -p cli --test golden_suite` and
  `INSTA_UPDATE=always cargo test -p frontend --test golden_expansion`.
- Add new `.lrl` fixtures under `cli/tests/golden/` to extend semantics coverage.
