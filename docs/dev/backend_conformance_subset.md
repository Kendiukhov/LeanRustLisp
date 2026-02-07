# Backend Conformance Subset

This document defines the stable, testable overlap used to compare dynamic and typed backends.

## MIR Semantic Truth (for this subset)

A program is in conformance when all of the following hold after MIR validation (typing + ownership + NLL):

1. The same validated MIR is used for both backends.
2. Observable behavior matches expected semantics:
- Exit code matches expected exit code.
- Canonical final result matches expected result (`nat:N` or `bool:true|false`).
- Non-result stdout lines match exactly.
3. Dynamic and typed backend observables are identical for the same MIR.

Harness location:
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/cli/tests/backend_conformance.rs`

## Prelude Compatibility Policy

By default, conformance tests use a minimal compatibility prelude:
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/conformance_prelude.lrl`

This prelude intentionally defines only shared core data needed by the subset (`Nat`, `Bool`).

Case-level prelude override is supported via metadata:
- `;;! prelude: <path>`

This is used for targeted API-layer checks when needed (for example, shared prelude `append` behavior).

Rationale:
- Full API+platform stacks still differ in runtime-oriented boundaries (`Dyn`/`EvalCap`/`eval`, runtime checks).
- The mission compares backend faithfulness to MIR semantics in the overlap, not prelude feature parity.

## Included Constructs (Overlap Subset)

Included and required to match:
- `Nat`, `Bool`
- Non-parameterized user ADTs
- Constructor application
- `match` / `switch`
- Nested `match`
- `let` and simple function calls
- Basic recursion over `Nat`

Current overlap corpus:
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/overlap`

## Excluded Constructs

Excluded from conformance matching (documented as tagged tests):
- Dynamic eval boundary (`Dyn`/`EvalCap` semantics)
- Interior mutability runtime checks (`RefCell`/`Mutex`/`Atomic` behavior)
- Indexed/runtime-check lowering edge cases not jointly stabilized
- Higher-order closure capture modes outside stable overlap
- Any program relying on known prelude representation differences

Excluded corpus:
- `/Volumes/Crucial X6/MacBook/Code/leanrustlisp/tests/backend_conformance/cases/excluded`

## Why These Exclusions Exist

- They require additional runtime contracts or backend-specific machinery that is not yet jointly specified and stabilized.
- Including them now would mix conformance bugs with intentionally incomplete feature work, reducing signal quality.
