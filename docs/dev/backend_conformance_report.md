# Backend Conformance Report

## Scope

- Harness: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/tests/backend_conformance.rs`
- Subset spec: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/docs/dev/backend_conformance_subset.md`
- Overlap tests: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap`
- Excluded tests: `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/excluded`

## Results

Command:
- `cargo test -p cli --test backend_conformance -- --test-threads=1`

Current status:
- Overlap-subset tests: 13 total, 13 matching, 0 failing
- Excluded tests: 4 (documented exclusions, not compared)

## Mismatch Triage History and Fixes

Initial conformance run found overlap mismatches in dynamic backend execution. Root causes and fixes:

1. Bool/Nat discriminant semantics mismatch
- Minimal repros:
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/bool_not.lrl`
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/bool_to_nat.lrl`
- Observed:
- Dynamic backend interpreted builtin discriminants inconsistently with ctor indices.
- Fix:
- Added `runtime_discriminant` and switched MIR discriminant/switch lowering to it in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/mir/src/codegen.rs`.
- Regression coverage:
- Bool and Nat overlap cases above now pass.

2. Builtin field projection mismatch (Nat/List)
- Minimal repros:
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/nat_pred.lrl`
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/nat_add_recursive.lrl`
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/nat_double.lrl`
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/nested_match_maybe.lrl`
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap/tree_sum_three.lrl`
- Observed:
- Dynamic backend projected fields only from `Value::Inductive`, but builtin runtime values (`Nat`, `List`) use specialized representations.
- Fix:
- Added `runtime_project_field` and routed field projection through it in `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/mir/src/codegen.rs`.
- Regression coverage:
- Nat recursion and nested/user-ADT overlap cases above now pass.

## Conformance Decision

- For the defined overlap subset, typed and dynamic backends are currently conformant to validated MIR semantics.
- Remaining excluded areas are intentionally documented and not treated as conformance failures.
