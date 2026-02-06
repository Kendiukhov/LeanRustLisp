# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-04 Round 13

This report is based on a fresh pass over the codebase and README contract, without relying on prior audit notes.

## Executive summary
- Macro boundary enforcement is present and blocks macro‑emitted `unsafe`/`axiom`/`import classical` forms under the default deny policy, aligning with the prelude boundary claim. (`frontend/src/macro_expander.rs:432`)
- **Blocker:** opaque aliases can hide `Ref` and interior‑mutability shapes from MIR lowering, so NLL creates no loans and runtime checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **Blocker:** opaque aliases to Prop bypass erasure and Prop‑elimination restrictions, allowing proof data to influence runtime. (`mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`, `kernel/src/checker.rs:3950`)
- Effect typing remains a call‑boundary check only; partial defs are not required to return `Comp`, contradicting the “effects show up in the type” promise. (`README.md:52`, `kernel/src/checker.rs:5142`)
- MIR typing treats `Opaque` as a wildcard outside refs, letting incompatible shapes slip through post‑kernel. (`mir/src/analysis/typing.rs:614`)
- Defeq is globally fuel‑bounded, so transparent unfolding can still DoS valid developments. (`README.md:37`, `kernel/src/nbe.rs:1011`)

## Contract violations
1. **Effects are promised in types but not enforced.** README claims effects “show up in the type,” yet the kernel only enforces call‑boundary restrictions and does not require `Comp` in the return type. (`README.md:52`, `kernel/src/checker.rs:5142`)
2. **Proof erasure can be bypassed via opaque Prop aliases.** README promises proof erasure; MIR erasure only acts on locals tagged `is_prop`, which is computed using reducible‑only whnf, so opaque Prop aliases are missed. (`README.md:49`, `mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)
3. **Rust‑grade borrow safety is bypassable.** README promises Rust‑grade ownership/borrowing; opaque aliases prevent `Ref` recognition in MIR lowering and NLL loan creation. (`README.md:50`, `mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

## Soundness / TCB risks
**Kernel soundness risks**
- **Prop elimination restriction ignores opaque aliases.** `check_elimination_restriction` determines `is_prop` from a syntactic `Sort 0` in the inductive’s result, without unfolding opaque aliases, enabling large elimination into Type for Prop‑like aliases. (`kernel/src/checker.rs:3950`)
- **Prop‑field rejection in data inductives ignores opaque aliases.** `check_inductive_soundness` uses the same non‑unfolding approach; Prop fields can be smuggled into data via opaque aliases. (`kernel/src/checker.rs:5001`)
- **Axiom tag tracking is best‑effort.** Axioms can be declared without tags, so “classical dependency” tracking is not robust against untagged classical axioms. (`frontend/src/declaration_parser.rs:242`)

**Compiler correctness / safety risks**
- **Borrow checking and IM runtime checks are keyed off MIR types only.** If lowering yields `MirType::Opaque`, NLL creates no loans and interior‑mutability checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **`MirType::Opaque` is a wildcard outside refs.** `types_compatible` returns `true` for any opaque pairing outside refs, letting mismatches pass to later stages. (`mir/src/analysis/typing.rs:614`)

## Semantic gaps (severity)
- **[High] Prop‑shape detection ignores opaque aliases.** Proof erasure and Prop‑elimination restrictions can be bypassed. (`mir/src/lower.rs:936`, `kernel/src/checker.rs:3950`)
- **[High] Borrow checking can be bypassed via opaque aliases.** Opaque aliases to `Ref` or `RefCell` skip loans and runtime checks. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **[High] Effect typing not enforced.** `partial def` does not require `Comp`. (`kernel/src/checker.rs:5142`)
- **[Medium] `Opaque` is a MIR typing wildcard.** Incompatible MIR shapes may pass. (`mir/src/analysis/typing.rs:614`)
- **[Medium] Defeq fuel DoS.** Legitimate terms can fail under default fuel. (`kernel/src/nbe.rs:1011`, `README.md:37`)
- **[Low] Axiom tags optional.** Classical dependency tracking can be evaded by omitting tags. (`frontend/src/declaration_parser.rs:242`)

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
1. **Add a “shape reducer” for borrow types.**
   - What: Unfold opaque aliases only to recognize `Ref` and interior‑mutability shapes during MIR lowering.
   - Where: `mir/src/lower.rs`.
   - Why: Prevent alias‑based borrow bypass.
   - Tests: opaque alias to `Ref Mut` still lowers to `MirType::Ref` and fails NLL on conflict.
2. **Create loans from `Rvalue::Ref` regardless of destination type.**
   - What: Base loan creation on the rvalue’s borrow, not `dest_ty`.
   - Where: `mir/src/analysis/nll.rs:567`.
   - Why: Ensure borrowing is tracked even when types are conservative.
   - Tests: opaque alias destination still triggers loan and conflict.
3. **Insert interior‑mutability checks at borrow sites.**
   - What: Generate runtime checks from borrow operations, not just local types.
   - Where: `mir/src/analysis/nll.rs:1333`.
   - Why: Opaque aliases can hide IMKind on locals.
   - Tests: opaque alias to `RefCell` yields `RefCellBorrow` checks.
4. **Prop‑shape detection that bypasses opacity.**
   - What: Introduce `is_prop_like` that unfolds opaque aliases for Prop classification only.
   - Where: `kernel/src/checker.rs`, `mir/src/lower.rs`.
   - Why: Enforce erasure and elimination restrictions correctly.
   - Tests: opaque Prop alias is erased; large elimination rejected.
5. **Apply Prop‑shape detection in inductive checks.**
   - What: Use `is_prop_like` for result sorts and constructor domain checks.
   - Where: `kernel/src/checker.rs:3950`, `kernel/src/checker.rs:5001`.
   - Why: Block Prop‑field smuggling.
   - Tests: data inductive with opaque Prop field rejected.
6. **Make `Opaque` typing strict outside refs.**
   - What: Require reason‑equality (or tagged equivalence) for `MirType::Opaque` compatibility.
   - Where: `mir/src/analysis/typing.rs:614`.
   - Why: Prevent post‑kernel MIR mismatches.
   - Tests: assignments between distinct opaque reasons rejected.
7. **Enforce `Comp` return type for `partial def`.**
   - What: Validate return type for partial definitions.
   - Where: `kernel/src/checker.rs`, `frontend/src/elaborator.rs`.
   - Why: Align with README’s effect‑in‑type promise.
   - Tests: `partial def` returning `Nat` fails; `Comp Nat` passes.
8. **Add strict axiom‑tag mode.**
   - What: CLI flag to reject untagged axioms when tracking is required.
   - Where: `cli/src/driver.rs`, `frontend/src/declaration_parser.rs`.
   - Why: Prevent axiom laundering.
   - Tests: strict mode rejects untagged axiom, accepts tagged.
9. **Improve defeq fuel diagnostics.**
   - What: Emit top‑level def names and transparency hints on fuel exhaustion.
   - Where: `kernel/src/nbe.rs`, `kernel/src/checker.rs`.
   - Why: Make DoS failures actionable.
   - Tests: fuel exhaustion prints culprit definitions.
10. **Add regression tests for opaque Prop and opaque Ref aliases.**
    - Where: `kernel/tests/*`, `mir/tests/*`, `cli/tests/*`.
    - Why: Lock in fixes.
11. **Document opacity vs Prop semantics.**
    - What: Explicitly state that opacity does not hide Prop for erasure/elimination.
    - Where: `docs/spec/core_calculus.md`, `docs/spec/kernel_boundary.md`.
    - Why: Prevent future regressions.
12. **Temporary lint for opaque borrow aliases.**
    - What: Warn on `opaque` aliases of `Ref`/`RefCell` until fixes land.
    - Where: `mir/src/lints.rs`.
    - Why: Short‑term safety net.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Opaque aliases cannot hide `Ref` or interior‑mutability shapes from MIR/NLL.
- [ ] Prop‑like types are erased and large‑elimination‑restricted even under opaque aliases.
- [ ] `partial def` enforces `Comp` (or README/spec updated to explicitly retract the claim).
- [ ] `MirType::Opaque` is not a wildcard in MIR typing.
- [ ] Defeq fuel exhaustion is diagnosable with actionable hints.

## Suggested GitHub issues (titles + labels)
- “Opaque aliases bypass borrow checking and interior‑mutability runtime checks” — labels: bug, soundness, mir
- “Opaque Prop aliases bypass erasure and Prop elimination restrictions” — labels: bug, soundness, kernel
- “Effect typing not enforced for partial defs (Comp missing)” — labels: design, kernel, docs
- “MIR typing treats Opaque as wildcard outside refs” — labels: bug, mir
- “Add strict axiom‑tag mode to prevent classical laundering” — labels: design, cli, kernel
- “Defeq fuel DoS: add trace + mitigation diagnostics” — labels: design, kernel, test
