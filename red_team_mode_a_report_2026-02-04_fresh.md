# Red Team Mode A Report (Semantic / Pre‑Codegen) — Fresh Audit — 2026-02-04

This report is a fresh audit produced directly from the codebase and README, without consulting prior audit documents.

## Executive summary
- Macro boundary scanning is implemented and blocks macro‑emitted `unsafe`/`axiom`/`import classical` forms by default, matching the prelude boundary story. (`frontend/src/macro_expander.rs:432`)
- Hygiene uses exact scope‑set equality; this is strong against capture but risks rejecting valid expansions and may hide hygiene bugs elsewhere. (`frontend/src/macro_expander.rs:288`)
- **Blocker:** opaque aliases can hide `Ref`/interior‑mutability shapes from MIR lowering, so NLL creates no loans and runtime checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **Blocker:** opaque aliases to `Prop` bypass both erasure and Prop‑elimination restrictions, enabling proof data to affect runtime. (`mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`, `kernel/src/checker.rs:3950`)
- Effect typing is still only a call‑boundary check; `partial def` is not required to return `Comp`, contradicting the “effects show in the type” claim in the README intro. (`README.md:52`, `kernel/src/checker.rs:5142`)
- MIR typing treats `Opaque` as a wildcard outside refs, so post‑kernel mismatches can slip through. (`mir/src/analysis/typing.rs:614`)
- Definitional equality is fuel‑bounded globally, so transparent unfolding can still DoS valid developments. (`README.md:37`, `kernel/src/nbe.rs:1011`)

## Stop‑the‑line list (prioritized)
1. Opaque aliases can bypass borrow checking and interior‑mutability runtime checks. Evidence: lowering treats opaque alias as `MirType::Opaque`, and NLL only creates loans / checks when the destination type is `MirType::Ref` / `MirType::InteriorMutable`. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
2. Opaque Prop aliases bypass erasure and Prop‑elimination restrictions, enabling proof‑data computation. Evidence: Prop detection uses `Transparency::Reducible` only, and elimination/field checks use `extract_pi_binders` without unfolding. (`mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`, `kernel/src/checker.rs:3950`, `kernel/src/checker.rs:5001`)
3. MIR typing treats `Opaque` as a wildcard, so inconsistent MIR can proceed to codegen. (`mir/src/analysis/typing.rs:614`)

## Safe‑to‑proceed checklist (if you insist on limited feature work)
- Only add features that do not introduce new type aliases around `Ref` or `RefCell`‑like types.
- Avoid any new Prop‑typed data or Prop‑indexed features until Prop‑shape detection is fixed.
- Keep macro extensions inside the existing boundary allowlist and avoid macro‑generated `axiom` or `import classical` forms.

## Contract violations
1. **Effects are promised as type‑level but not enforced.** README states effects “show up in the type” for the computational fragment, but kernel enforcement only checks which definitions are called, not the return type. (`README.md:52`, `kernel/src/checker.rs:5142`)
2. **Proof erasure can be bypassed.** README promises proof erasure; MIR erasure only acts on locals already flagged `is_prop`, which is computed via reducible‑only whnf. Opaque Prop aliases evade the flag. (`README.md:49`, `mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)
3. **Rust‑grade borrowing is bypassable via opacity.** README promises Rust‑grade resource discipline; opaque aliases prevent `Ref` recognition during lowering and NLL loan creation. (`README.md:50`, `mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

## Soundness / TCB risks
**Kernel soundness risks**
- Prop‑elimination restriction depends on syntactic `Sort 0` in `decl.ty` and does not unfold opaque aliases, so Prop‑like inductives can be treated as data. (`kernel/src/checker.rs:3950`)
- Prop‑field rejection in data inductives uses the same non‑unfolding path, so Prop fields can be smuggled into data via opaque aliases. (`kernel/src/checker.rs:5001`)

**Compiler correctness / safety risks**
- Borrow checking and runtime checks are keyed off lowered `MirType` only; if lowering produces `MirType::Opaque`, NLL creates no loans and `RefCell`/`Mutex` checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- `MirType::Opaque` is treated as compatible with any non‑reference type, allowing mismatches after kernel validation. (`mir/src/analysis/typing.rs:614`)

## Semantic gaps (severity)
- [High] Prop‑shape detection ignores opaque aliases, breaking erasure and Prop‑elimination rules. (`mir/src/lower.rs:936`, `kernel/src/checker.rs:3950`)
- [High] Borrow checking and interior‑mutability checks can be bypassed via opaque aliases. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- [High] Effect typing is not enforced; partial defs do not require `Comp`. (`kernel/src/checker.rs:5142`)
- [Medium] `Opaque` is a wildcard in MIR typing outside refs. (`mir/src/analysis/typing.rs:614`)
- [Medium] Defeq fuel is a global DoS lever for valid terms. (`kernel/src/nbe.rs:1011`, `README.md:37`)
- [Low] Axiom tags are optional; classical axioms can be declared untagged, weakening tracking. (`frontend/src/declaration_parser.rs:242`)

## Minimal reproducible examples
1. **Opaque alias hides `Ref` from NLL (should be rejected):**
```lisp
(opaque MyRef (sort 1) (Ref Mut Nat))

(def demo (pi x Nat Nat)
  (lam x Nat
    (let r MyRef (borrow_mut x)
      x)))
```
Evidence: `MyRef` does not unfold under reducible whnf in MIR lowering, so `dest_ty` is `MirType::Opaque` and no loan is created. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

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
Evidence: Prop detection uses reducible whnf and `extract_pi_binders` without unfolding, so `Bad` is treated as data and the match computes runtime data. (`kernel/src/checker.rs:3950`, `mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)

3. **Partial def without effect type:**
```lisp
(partial loop (pi n Nat Nat)
  (lam n Nat (loop n)))
```
Evidence: effect checking only enforces call‑boundary restrictions, not `Comp` in the return type. (`kernel/src/checker.rs:5142`)

4. **Untagged classical axiom (tracking bypass):**
```lisp
(axiom choice (pi P (sort 0) P))
```
Evidence: axiom tags are optional when the form has only 3 arguments. (`frontend/src/declaration_parser.rs:242`)

## Fix plan (prioritized)
1. What: add a “shape reducer” that unfolds opaque aliases only for recognizing `Ref` and interior‑mutable forms. Where: `mir/src/lower.rs:291`. Why: prevent borrow‑shape bypass. Tests: add an opaque alias to `Ref Mut` that still lowers to `MirType::Ref` and fails NLL.
2. What: create loans based on `Rvalue::Ref` regardless of destination type, or require the rvalue’s source type when lowering. Where: `mir/src/analysis/nll.rs:567`. Why: ensure borrow creation is not gated on `MirType` of dest. Tests: `borrow_mut` into opaque alias triggers a conflict.
3. What: insert interior‑mutability runtime checks at borrow sites, not only by local type. Where: `mir/src/analysis/nll.rs:1333`. Why: aliases can hide IMKind in locals. Tests: opaque alias to `RefCell` still yields `RefCellBorrow` checks.
4. What: strengthen `Opaque` compatibility to require matching opaque reasons even outside refs. Where: `mir/src/analysis/typing.rs:614`. Why: stop post‑kernel MIR mismatches. Tests: assignment between different opaque reasons is rejected.
5. What: define `is_prop_like` that unfolds opaque aliases (or uses a cached attribute) for Prop checks only. Where: `mir/src/lower.rs:936`, `kernel/src/checker.rs:3950`. Why: keep defeq opacity but enforce Prop semantics. Tests: opaque Prop alias is erased and large elimination is rejected.
6. What: in `check_inductive_soundness`, use `is_prop_like` on constructor domains and result sorts. Where: `kernel/src/checker.rs:5001`. Why: prevent Prop‑field smuggling. Tests: a data inductive with an opaque‑Prop field is rejected.
7. What: enforce `partial def` return type to be `Comp A` (or effect‑typed) during definition checking. Where: `kernel/src/checker.rs:5142`, `frontend/src/elaborator.rs`. Why: align with README’s effect‑in‑type claim. Tests: partial def returning `Nat` fails, `Comp Nat` passes.
8. What: add a strict mode that rejects untagged axioms when classical/unsafe tracking is required. Where: `frontend/src/declaration_parser.rs:242`, `cli/src/driver.rs`. Why: prevent axiom laundering. Tests: `--require-axiom-tags` rejects untagged axioms.
9. What: include top‑level def names in defeq fuel exhaustion diagnostics. Where: `kernel/src/nbe.rs:1011` and error mapping in `kernel/src/checker.rs`. Why: actionable DoS mitigations. Tests: fuel exhaustion prints culprit definitions.
10. What: add regression tests for opaque Ref alias and opaque Prop alias in CLI or MIR tests. Where: `cli/tests/`, `mir/tests/`. Why: lock in fixes. Tests: `opaque` alias to `Ref` fails borrow; opaque Prop alias does not allow `match` to compute data.
11. What: document the “opacity does not hide Prop for erasure” rule in the spec. Where: `docs/spec/core_calculus.md`, `docs/spec/kernel_boundary.md`. Why: prevent future regressions.
12. What: add a linter that flags opaque aliases of `Ref`/`RefCell` until shape‑reducer lands. Where: `mir/src/lints.rs`. Why: short‑term safety net.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Opaque aliases cannot hide `Ref` or interior‑mutability shapes from MIR/NLL.
- [ ] Prop‑like types are erased and large‑elimination‑restricted even under `opaque` aliases.
- [ ] `partial def` requires `Comp` (or the README/Spec are updated to explicitly retract the claim).
- [ ] `MirType::Opaque` is not a wildcard in MIR typing.
- [ ] Defeq fuel exhaustion diagnostics are actionable for large unfolding.

## Suggested GitHub issues (titles + labels)
- “Opaque aliases bypass borrow checking and interior‑mutability runtime checks” — labels: bug, soundness, mir
- “Opaque Prop aliases bypass erasure and Prop elimination restrictions” — labels: bug, soundness, kernel
- “Effect typing not enforced for partial defs (Comp missing)” — labels: design, kernel, docs
- “MIR typing treats Opaque as wildcard outside refs” — labels: bug, mir
- “Add strict axiom‑tag mode to prevent classical laundering” — labels: design, cli, kernel
- “Defeq fuel DoS: add trace + mitigation diagnostics” — labels: design, kernel, test
