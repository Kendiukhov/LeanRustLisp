# Parallel Streams — Round 19 Follow-ups (Pre‑Codegen)

Goal: address Round 19 findings with minimal overlap. Where an issue can be resolved by **documentation/spec alignment**, we do that; otherwise we implement the smallest correct code change + a regression test.

## Stream 1 — Kernel defeq: lifetime-label correctness (**code + tests**)
**Owner:** Kernel Guardian  
**Why not docs-only:** this is a semantic hole; MIR relies on labels for regions.

Tasks:
1) Preserve `Term::App` labels when building application spines used in defeq (e.g., `collect_app_spine`).
2) Make defeq label-aware for `Ref` applications (or, simplest: compare labels for all spine items when present).
3) Add kernel-level test: `Ref #[a] Shared Nat` is **not** defeq to `Ref #[b] Shared Nat`.
4) Add CLI negative test: the `coerce` example must fail with a clear “label mismatch” diagnostic.

Acceptance:
- The red-team “lifetime laundering” repro fails.
- Kernel test suite contains a non-ignored regression for label-sensitive defeq.

---

## Stream 2 — MIR/NLL coverage for labeled lifetimes (**tests only**)
**Owner:** Tester (Semantics mode)  
**Docs-only?** No; needs regression tests.

Tasks:
1) Add MIR corpus cases where a returned reference must be tied to an input label (positive + negative).
2) Add higher-order call-flow cases (passing labeled refs through closures) ensuring labels survive: surface → core → MIR.
3) Ensure tests run in CI and fail if labels are dropped/unified.

Acceptance:
- New corpus tests pass and cover label-preservation end-to-end.

---

## Stream 3 — Capture-mode enforcement boundary (**doc-first, optional code**)
**Owner:** Production-grade engineer (docs) + Borrow Architect (if code change needed)  
**Docs-only?** Often yes, if behavior is already correct and only the “TCB story” is inconsistent.

Tasks (Doc-first):
1) Update docs/spec/kernel_boundary.md and docs/spec/phase_boundaries.md to state precisely:
   - what the kernel validates about capture modes (e.g., conservative minimum-kind checks)
   - what MIR recomputes/enforces (capture strength, region instantiation)
2) Add a short “TCB note”: capture-mode strength must be enforced either (a) conservatively in kernel, or (b) purely in MIR with kernel not trusting annotations.

Optional code task (only if current behavior is unsound):
- If kernel currently accepts an annotation that MIR later “tightens,” add a kernel-side conservative validation that rejects too-weak capture modes.

Acceptance:
- Docs match reality; no unresolved “kernel trusts MIR-only semantics” ambiguity.

---

## Stream 4 — Interior mutability stubs (**docs + gating policy**)
**Owner:** Production-grade engineer (policy/docs)  
**Docs-only?** Mostly yes *if* these features are already explicitly gated to `unsafe`/`noncomputable`. If they are reachable from “safe” code, then code gating is required.

Tasks:
1) Confirm the current policy: RefCell/Mutex are either:
   - explicitly `unsafe`/`noncomputable` to execute, OR
   - forbidden in “safe mode” until runtime checks exist.
2) Update README + docs/production.md:
   - clearly state that runtime checks are not implemented yet (or are no-ops) and therefore the feature is gated.
3) Add a linter/profile rule (panic-free profile) to flag any interior mutability usage in safe builds (if not already present).

Optional code task:
- If RefCell/Mutex can be used in safe total defs without gating, add a compile-time error (“not supported in safe mode until runtime checks implemented”).

Acceptance:
- No user can rely on “may panic” behavior without opting into the explicit gated mode.
- Docs make the status unambiguous.

---

## Stream 5 — Macro hygiene policy (subset vs equality) (**docs + one regression test**)
**Owner:** Macro Hygienist  
**Docs-only?** Depends: if you intentionally changed the hygiene model, update docs; if not, fix code. Start with docs + a test that locks intended behavior.

Tasks:
1) Decide and document the intended hygiene resolution rule:
   - exact scope equality **or**
   - subset-compatible scopes (Racket-like)
2) Add the nested macro regression from Round 19 (`outer/inner`) to `frontend/tests`.
3) Ensure spec (`docs/spec/macro_system.md`) matches the implemented rule.

Acceptance:
- One authoritative doc statement + one regression test; implementation matches.

---

## Stream 6 — Release-bar updater (**docs only**)
**Owner:** Release-bar auditor / docs maintainer  
**Docs-only:** yes.

Tasks:
1) Add “Ref lifetime labels participate in defeq” to the release bar checklist.
2) Add “labels preserved core→MIR” and “label laundering negative test exists” to checklist.
3) Link the tests introduced in Streams 1–2.

Acceptance:
- Release-bar doc reflects new invariants; future audits are consistent.

---

## Coordination rules (avoid overlap)
- Stream 1 owns **kernel defeq label semantics**. Others must not touch defeq logic.
- Stream 2 adds only tests; does not change lowering/defeq.
- Stream 5 owns macro hygiene decision + doc/test; it should not change unrelated frontend phases.
- Stream 4 is policy/docs and optional gating; no interpreter/codegen implementation work in this round.
