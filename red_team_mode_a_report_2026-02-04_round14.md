# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-04 Round 14

This report is based on a fresh audit of the codebase and README contract. No prior audit documents were consulted.

## Executive summary
- Macro boundary enforcement exists and blocks macro‑emitted `unsafe`/`axiom`/`import classical` forms under the default deny policy, matching the stated prelude boundary. (`frontend/src/macro_expander.rs:432`)
- **Blocker:** opaque aliases can hide `Ref` and interior‑mutability shapes during MIR lowering, so NLL creates no loans and runtime checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **Blocker:** opaque aliases to Prop bypass both erasure and Prop‑elimination restrictions, letting proof data influence runtime results. (`mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`, `kernel/src/checker.rs:3950`)
- Effect typing is still enforced only as call‑boundary checks; `partial def` is not required to return `Comp`, conflicting with the “effects show in the type” promise. (`README.md:52`, `kernel/src/checker.rs:5142`)
- MIR typing treats `Opaque` as a wildcard outside refs, allowing mismatches after kernel validation. (`mir/src/analysis/typing.rs:614`)
- Definitional equality is globally fuel‑bounded, so transparent unfolding can still DoS valid developments. (`README.md:37`, `kernel/src/nbe.rs:1011`)

## Contract violations
1. **Effect typing promised in types is not enforced.** README claims effects “show up in the type,” but the kernel only enforces call‑boundary checks. (`README.md:52`, `kernel/src/checker.rs:5142`)
2. **Proof erasure can be bypassed via opaque Prop aliases.** Erasure only applies to locals marked `is_prop`, which is computed via reducible‑only whnf; opaque Prop aliases evade it. (`mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)
3. **Rust‑grade borrow safety can be bypassed with opaque aliases.** Opaque aliases prevent `Ref` recognition in MIR lowering and NLL loan creation. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

## Soundness / TCB risks
**Kernel soundness**
- **Prop‑elimination restriction ignores opaque aliases.** `check_elimination_restriction` determines `is_prop` from a syntactic `Sort 0` result, without unfolding opaque aliases. (`kernel/src/checker.rs:3950`)
- **Prop‑field rejection in data inductives ignores opaque aliases.** `check_inductive_soundness` uses the same non‑unfolding path; Prop fields can be smuggled via opaque aliases. (`kernel/src/checker.rs:5001`)
- **Axiom tags are optional.** Classical axioms can be declared untagged, weakening dependency tracking. (`frontend/src/declaration_parser.rs:242`)

**Compiler correctness / safety**
- **Borrow checking and IM runtime checks are keyed off MIR types only.** If lowering yields `MirType::Opaque`, NLL creates no loans and interior‑mutability checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **`MirType::Opaque` is a wildcard outside refs.** `types_compatible` returns `true` for opaque mismatches outside refs. (`mir/src/analysis/typing.rs:614`)

## Semantic gaps (severity)
- **[High] Prop‑shape detection ignores opaque aliases.** Erasure and Prop‑elimination restrictions can be bypassed. (`mir/src/lower.rs:936`, `kernel/src/checker.rs:3950`)
- **[High] Borrow checking can be bypassed via opaque aliases.** Opaque aliases to `Ref`/`RefCell` skip loans and runtime checks. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **[High] Effect typing not enforced.** `partial def` does not require `Comp`. (`kernel/src/checker.rs:5142`)
- **[Medium] `Opaque` is a MIR typing wildcard outside refs.** Incompatible MIR shapes may pass. (`mir/src/analysis/typing.rs:614`)
- **[Medium] Defeq fuel DoS.** Valid developments can fail under default fuel. (`kernel/src/nbe.rs:1011`, `README.md:37`)
- **[Low] Axiom tags optional.** Classical dependency tracking is best‑effort only. (`frontend/src/declaration_parser.rs:242`)

## Minimal reproducible examples
1. **Opaque alias hides `Ref` from NLL (should be rejected):**
```lisp
(opaque MyRef (sort 1) (Ref Mut Nat))

(def demo (pi x Nat Nat)
  (lam x Nat
    (let r MyRef (borrow_mut x)
      x)))
```
Evidence: opaque alias lowers to `MirType::Opaque`; loans are only created when destination type is `MirType::Ref`. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

2. **Opaque Prop alias bypasses large elimination + erasure:**
```lisp
(opaque MyProp (sort 1) (sort 0))

(inductive Bad MyProp
  (ctor left Bad)
  (ctor right Bad))

(def to_nat (pi p Bad Nat)
  (lam p Bad
    (match p Nat
      (case (left) zero)
      (case (right) (succ zero)))))
```
Evidence: Prop classification uses reducible‑only whnf, so `Bad` is treated as data and the match computes runtime data. (`kernel/src/checker.rs:3950`, `mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)

3. **Partial def without effect type (contract mismatch):**
```lisp
(partial loop (pi n Nat Nat)
  (lam n Nat (loop n)))
```
Evidence: effect checking only enforces call‑boundary restrictions; no `Comp` requirement exists. (`kernel/src/checker.rs:5142`)

4. **Untagged classical axiom (tracking bypass):**
```lisp
(axiom choice (pi P (sort 0) P))
```
Evidence: axiom tags are optional when only 3 arguments are provided. (`frontend/src/declaration_parser.rs:242`)

## Fix plan (prioritized)
1. **Borrow‑shape reducer for aliases.**
   - What: Unfold opaque aliases only to detect `Ref` and interior‑mutability shapes during MIR lowering.
   - Where: `mir/src/lower.rs`.
   - Why: Prevent borrow‑shape bypass.
   - Tests: opaque alias to `Ref Mut` still lowers to `MirType::Ref` and fails borrow conflicts.
2. **Loan creation based on `Rvalue::Ref`, not destination type.**
   - What: Create loans for borrow operations regardless of `dest_ty`.
   - Where: `mir/src/analysis/nll.rs:567`.
   - Why: Avoid alias‑based loan bypass.
   - Tests: `borrow_mut` into opaque alias triggers conflict.
3. **Interior‑mutability checks at borrow sites.**
   - What: Insert runtime checks from borrow operations rather than local type inspection.
   - Where: `mir/src/analysis/nll.rs:1333`.
   - Why: Opaque aliases can hide IMKind on locals.
   - Tests: opaque alias to `RefCell` still yields `RefCellBorrow` checks.
4. **Prop‑shape detection that ignores opacity for semantics.**
   - What: Add `is_prop_like` using a special unfolding policy for Prop classification only.
   - Where: `kernel/src/checker.rs`, `mir/src/lower.rs`.
   - Why: Enforce erasure and Prop‑elimination restrictions.
   - Tests: opaque Prop alias is erased; large elimination rejected.
5. **Use Prop‑shape detection in inductive checks.**
   - What: Apply `is_prop_like` to result sorts and constructor domains.
   - Where: `kernel/src/checker.rs:3950`, `kernel/src/checker.rs:5001`.
   - Why: Prevent Prop‑field smuggling.
   - Tests: data inductive with opaque Prop field rejected.
6. **Make `Opaque` compatibility strict outside refs.**
   - What: Require reason‑equality (or compatible tag) for `MirType::Opaque` even outside refs.
   - Where: `mir/src/analysis/typing.rs:614`.
   - Why: Prevent post‑kernel MIR mismatches.
   - Tests: assignment between distinct opaque reasons fails.
7. **Enforce `Comp` for `partial def`.**
   - What: Validate that partial definitions return `Comp A` (or explicit effect type).
   - Where: `kernel/src/checker.rs`, `frontend/src/elaborator.rs`.
   - Why: Align with README effect promise.
   - Tests: partial def returning `Nat` fails; `Comp Nat` passes.
8. **Strict axiom‑tag mode.**
   - What: CLI flag to reject untagged axioms when tracking matters.
   - Where: `cli/src/driver.rs`, `frontend/src/declaration_parser.rs`.
   - Why: Prevent classical axiom laundering.
   - Tests: strict mode rejects untagged axioms.
9. **Improve defeq fuel diagnostics.**
   - What: Include top‑level def names and transparency hints on fuel exhaustion.
   - Where: `kernel/src/nbe.rs`, `kernel/src/checker.rs`.
   - Why: Actionable DoS mitigation.
   - Tests: fuel exhaustion message includes culprit definitions.
10. **Add regression tests for opaque Ref/Prop aliases.**
    - Where: `kernel/tests/*`, `mir/tests/*`, `cli/tests/*`.
    - Why: Lock in fixes.
11. **Document opacity vs Prop semantics.**
    - What: State that opacity does not hide Prop for erasure/elimination.
    - Where: `docs/spec/core_calculus.md`, `docs/spec/kernel_boundary.md`.
12. **Temporary lint for opaque borrow aliases.**
    - What: warn on `opaque` aliases of `Ref`/`RefCell` until fixes land.
    - Where: `mir/src/lints.rs`.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Opaque aliases cannot hide `Ref` or interior‑mutability shapes from MIR/NLL.
- [ ] Prop‑like types are erased and large‑elimination‑restricted even under opaque aliases.
- [ ] `partial def` enforces `Comp` (or README/spec updated to retract the claim).
- [ ] `MirType::Opaque` is not a wildcard in MIR typing.
- [ ] Defeq fuel exhaustion is diagnosable with actionable hints.

## Suggested GitHub issues (titles + labels)
- “Opaque aliases bypass borrow checking and interior‑mutability runtime checks” — labels: bug, soundness, mir
- “Opaque Prop aliases bypass erasure and Prop elimination restrictions” — labels: bug, soundness, kernel
- “Effect typing not enforced for partial defs (Comp missing)” — labels: design, kernel, docs
- “MIR typing treats Opaque as wildcard outside refs” — labels: bug, mir
- “Add strict axiom‑tag mode to prevent classical laundering” — labels: design, cli, kernel
- “Defeq fuel DoS: add trace + mitigation diagnostics” — labels: design, kernel, test
