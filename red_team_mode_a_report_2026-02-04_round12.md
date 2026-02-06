# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-04 Round 12

## Executive summary
- Macro hygiene now enforces exact scope matching, which hardens capture prevention. (`frontend/src/macro_expander.rs:288`)
- Macro boundary scanning still flags unsafe/classical/axiom forms emitted by macros (good alignment with the prelude boundary). (`frontend/src/macro_expander.rs:432`)
- **Blocker remains:** opaque aliases can hide `Ref` and interior‑mutability shapes from MIR lowering, so NLL never creates loans and runtime checks are skipped. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **New high‑risk gap:** opaque aliases to `Prop` are not recognized as Prop for erasure or elimination restrictions, so proof data can reach runtime and large elimination can slip into Type. (`mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`, `kernel/src/checker.rs:3950`)
- Effect typing is still only a call‑boundary check; partial defs are not required to return `Comp`, contradicting README promises. (`README.md:25`, `kernel/src/checker.rs:789`)
- MIR typing still treats `Opaque` as a wildcard (outside refs), allowing incompatible shapes to pass post‑kernel. (`mir/src/analysis/typing.rs:614`)
- Defeq remains fuel‑bounded globally; transparent unfolding can still DoS valid developments. (`kernel/src/nbe.rs:1011`, `README.md:37`)

## Contract violations
1. **Effect typing promised in types is not enforced.** README explicitly says partial defs “live under an effect (e.g., `Comp`)” and that effects “show up in the type,” but the kernel only enforces call‑boundary checks and never verifies a `Comp` return type. (`README.md:25`, `README.md:52`, `kernel/src/checker.rs:789`, `kernel/src/checker.rs:5142`)
2. **Proof erasure is bypassable via opaque Prop aliases.** README promises proof erasure; MIR only erases locals flagged `is_prop`, which is computed via `whnf` under `Transparency::Reducible`. An opaque alias to Prop will not be flagged and will survive into runtime. (`README.md:49`, `mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)
3. **Rust‑grade borrow safety can be bypassed with opaque aliases.** Lowering only recognizes `Ref`/interior‑mutable shapes after `Reducible` whnf; opaque aliases lower to `MirType::Opaque`, and NLL only creates loans for `MirType::Ref`. (`README.md:50`, `mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

## Soundness / TCB risks
**Kernel soundness**
- **Prop restrictions are syntactic and ignore opaque aliases (High).** `check_elimination_restriction` decides “is Prop” by peeling Pis and checking for a literal `Sort 0`. Opaque aliases to Prop are treated as non‑Prop, enabling large elimination into Type and proof‑data computation. (`kernel/src/checker.rs:3950`)
- **Inductive Prop field checks can be bypassed with opaque Prop aliases (High).** `check_inductive_soundness` uses the same `extract_pi_binders` logic, so Prop fields can be smuggled into data inductives by hiding Prop behind an opaque alias. (`kernel/src/checker.rs:5002`)
- **Classical axiom tracking is trust‑based (Medium).** Axiom tags are optional at the parser level; an untagged classical axiom is indistinguishable from a constructive one. (`frontend/src/declaration_parser.rs:252`)

**Compiler correctness / safety**
- **Opaque alias hides `Ref` / interior mutability (High).** MIR lowering emits `MirType::Opaque`, so NLL creates no loans and runtime checks are skipped; this is a direct bypass of the safety model. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`, `mir/src/analysis/nll.rs:1333`)
- **`Opaque` is treated as a wildcard in MIR typing (Medium).** `types_compatible` returns `true` whenever either side is `Opaque` (outside refs), allowing post‑kernel MIR inconsistencies to proceed to codegen. (`mir/src/analysis/typing.rs:614`)

## Semantic gaps (severity)
- **[High] Prop erasure + elimination restrictions can be bypassed via opaque aliases.** Proofs can influence runtime values, violating proof‑irrelevance/erasure expectations.
- **[High] Borrow checking can be bypassed via opaque aliases to `Ref` or `RefCell`/`Mutex`.** No loans or runtime checks are generated.
- **[High] Effect typing not enforced for partial definitions.** `partial def` does not require `Comp`, despite the stated design contract.
- **[Medium] MIR typing treats `Opaque` as a wildcard.** Inconsistent MIR may be accepted after kernel checking.
- **[Medium] Classical axiom tracking can be laundered by omitting tags.** Dependency reporting is only as strong as user honesty.
- **[Medium] Defeq fuel remains a global DoS lever.** Large transparent unfolding still fails valid terms under default fuel.

## Minimal reproducible examples
1. **Opaque alias hides `Ref` from NLL (should be rejected):**
```lisp
(opaque MyRef (sort 1) (Ref Mut Nat))

(def demo (pi x Nat Nat)
  (lam x Nat
    (let r MyRef (borrow_mut x)
      x)))
```
Evidence: opaque alias lowers to `MirType::Opaque`; loans are only created for `MirType::Ref`. (`mir/src/lower.rs:291`, `mir/src/analysis/nll.rs:567`)

2. **Opaque Prop alias defeats erasure + large elimination (proof data used at runtime):**
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
`Bad` is treated as non‑Prop because `MyProp` does not reduce under `Reducible`; elimination into `Nat` is accepted and proof data survives erasure. (`kernel/src/checker.rs:3950`, `mir/src/lower.rs:936`, `mir/src/transform/erasure.rs:4`)

3. **Partial def without effect type (contract mismatch):**
```lisp
(partial loop (pi n Nat Nat)
  (lam n Nat (loop n)))
```
Kernel only enforces call‑boundary checks; no `Comp` requirement is enforced. (`kernel/src/checker.rs:789`, `kernel/src/checker.rs:5142`)

4. **Classical axiom laundering via missing tag:**
```lisp
(axiom choice (pi P (sort 0) P))
```
No `classical` tag is required, so dependency tracking will not report this as classical. (`frontend/src/declaration_parser.rs:252`)

## Fix plan (prioritized)
1. **Borrow‑shape unfolding for aliases.** What: add a “shape‑only” reducer that unfolds `opaque` aliases when checking for `Ref`/interior‑mutable shapes. Where: `mir/src/lower.rs:291`. Why: prevent alias‑based borrow bypass. Tests: add an opaque `Ref` alias that still lowers to `MirType::Ref` and triggers NLL errors.
2. **Loan creation on `Rvalue::Ref` regardless of destination type.** What: create loans based on the rvalue, not just `dest` type. Where: `mir/src/analysis/nll.rs:567`. Why: avoid aliasing holes when type lowering is conservative. Tests: `borrow_mut` into opaque alias should still be rejected.
3. **Interior‑mutability runtime checks on borrow operations.** What: insert checks at borrow sites instead of relying on local type. Where: `mir/src/analysis/nll.rs:1333`. Why: opaque aliases can hide IMKind; borrow sites are the semantic ground truth. Tests: opaque alias to `RefCell` still yields runtime checks.
4. **Opaque typing strictness.** What: make `types_compatible` require reason‑equality (or tagged equivalence) even outside refs. Where: `mir/src/analysis/typing.rs:614`. Why: prevent post‑kernel MIR inconsistencies. Tests: assignments between distinct opaque reasons rejected.
5. **Prop‑shape classifier independent of transparency.** What: add `is_prop_like(term)` using `Transparency::All` (or a cached attribute) for erasure and elimination checks only. Where: `mir/src/lower.rs:936`, `kernel/src/checker.rs:3950`. Why: avoid proof‑data leaks while preserving `opaque` defeq behavior. Tests: opaque Prop alias still erased; large elimination rejected.
6. **Enforce Prop restrictions using whnf.** What: in `check_elimination_restriction` and `check_inductive_soundness`, whnf the result sort (with a “Prop‑shape” rule) before deciding `is_prop`. Where: `kernel/src/checker.rs:3950`, `kernel/src/checker.rs:5002`. Why: prevent Prop‑field smuggling through aliases. Tests: `Bad` example above is rejected.
7. **Effect typing enforcement.** What: require `partial def` to return `Comp A` (or an explicit effect type) at definition time. Where: `kernel/src/checker.rs:789`, `frontend/src/elaborator.rs`. Why: align with README contract. Tests: partial def returning `Nat` fails; `Comp Nat` passes.
8. **Axiom tag enforcement mode.** What: add a CLI flag (e.g., `--require-axiom-tags`) that rejects untagged axioms for classical/unsafe tracking. Where: `frontend/src/declaration_parser.rs:252`, `cli/src/driver.rs`. Why: prevent tag laundering in high‑assurance mode. Tests: untagged axiom rejected under the flag.
9. **Defeq fuel diagnostics with actionable trace.** What: include top‑level def names and transparency hints when fuel is exhausted. Where: `kernel/src/nbe.rs:1011`, `kernel/src/checker.rs:2963`. Why: make DoS failures debuggable. Tests: a large unfold case reports the dominant definitions.
10. **Prop erasure regression tests.** What: add tests ensuring opaque Prop aliases are still erased and cannot be pattern‑matched into data. Where: `mir/tests/`, `cli/tests/`. Why: prevent regressions once Prop‑shape fix lands.
11. **Borrow‑shape alias tests for interior mutability.** What: add `opaque` alias to `RefCell` and ensure runtime checks are inserted. Where: `mir/tests/borrowck_corpus.rs`. Why: cover IMKind/alias interactions.
12. **Document the “opaque vs Prop” policy.** What: update spec with explicit rules: opacity does not hide Prop for erasure/elimination. Where: `docs/spec/core_calculus.md`, `docs/spec/kernel_boundary.md`. Why: align spec with enforcement.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Opaque aliases cannot hide `Ref` / interior‑mutable shapes from MIR/NLL.
- [ ] Prop‑like types are erased and large‑elimination‑restricted even under `opaque`.
- [ ] `partial def` requires `Comp` (or docs explicitly retract the guarantee).
- [ ] `Opaque` is not a MIR typing wildcard.
- [ ] Axiom tagging policy is enforced or explicitly documented as best‑effort.
- [ ] Defeq fuel exhaustion produces actionable diagnostics.

## Suggested GitHub issues (titles + labels)
- “Opaque aliases can bypass borrow checking and IM runtime checks” — labels: bug, soundness, mir
- “Opaque Prop aliases bypass erasure and Prop elimination restrictions” — labels: bug, soundness, kernel
- “Effect typing not enforced for partial defs (Comp missing)” — labels: design, kernel, docs
- “MIR typing treats Opaque as wildcard outside refs” — labels: bug, mir
- “Add strict axiom‑tag enforcement mode to prevent classical laundering” — labels: design, cli, kernel
- “Defeq fuel DoS: add trace + per‑def mitigation guidance” — labels: design, kernel, test
