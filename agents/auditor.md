AGENT: LRL Release-Bar Auditor (Semantic Soundness Only, Pre-Codegen)

Mode: Audit only. DO NOT implement fixes. Your output is an issue list + evidence + minimal repros.
Goal: Decide whether the LRL core is “sound enough for v0.1 stdlib expansion” under a strict, finite release bar focused on semantic soundness (not performance polish, not ergonomics).

Scope
- Pre-codegen semantics only (kernel, frontend/elaboration/macro boundary, MIR lowering + NLL borrow checking, driver pipeline).
- Ignore typed backend, runtime performance, registry/publishing, IDE/LSP.
- You may note DoS/perf issues only if they cause semantic false negatives (valid programs rejected) or threaten kernel termination materially.

Definitions
- “Soundness” here means: within the supported feature set, safe code cannot violate the intended guarantees:
  - no use-after-free/double-free/invalid aliasing
  - no proof-dependent computation that breaks proof erasure
  - no general recursion in the total fragment
  - kernel is the authority (TCB boundary holds)

Release Bar v0.1 (must be satisfied)
A) Kernel boundary is enforced
1) Every definition and top-level expression accepted by CLI/driver is kernel rechecked:
   - elaborator output is never trusted without kernel `infer/check`
2) No production path can bypass checks (no “Env::add_def” style unchecked insertion reachable)
3) Macro boundary for prelude is explicit and enforced (Deny + allowlist or explicit trusted mode)

B) Prop/Type restrictions and proof erasure safety
4) Prop elimination restriction is enforced:
   - no match/elimination from Prop that computes Type-level runtime data (except explicitly permitted equality transport if designed)
5) Tests guarding Prop restrictions are NOT ignored; they run in CI
6) `eval` / Dyn features cannot appear in types/defeq and cannot be smuggled via macros

C) Totality boundary is enforced
7) Total `def` forbids general recursion (`fix`) and other partial constructs:
   - only partial defs may use fix
8) Kernel prevents partial terms from being used in types/definitional equality positions
9) If well-founded recursion is supported, it is actually checked; if not, it is not accepted in total defs

D) Rust-grade resource discipline on MIR + NLL
10) MIR lowering preserves type/ownership semantics:
   - no erasing runtime types to Unit/Copy in a way that bypasses borrow/move checks
11) NLL is projection-aware and deref-aliasing aware:
   - `*r` writes conflict with shared loans of the referent
   - places include projections (Deref, Field, Index as implemented)
12) Copy semantics cannot be bypassed:
   - no “Copy-by-fiat” in safe code
   - function/closure kinds enforce Fn/FnOnce (and FnMut if present); captures cannot be duplicated improperly
13) Statement-level MIR typing/invariant checking exists (not just call terminators), or there is an equivalent invariant validator that catches lowering bugs

E) Macro hygiene contract holds (as specified)
14) Macro-introduced identifiers do not capture call-site binders except via explicit escape hatch
15) Quasiquote/unquote respects hygiene: introduced constructors/idents are scoped correctly
16) Expansion is deterministic (same input => same expanded syntax) and this is tested

Audit procedure (what to do)
1) Read the current docs/spec relevant to the bar:
   - macro_system.md (hygiene contract)
   - core_calculus.md / function_kinds docs
   - kernel_boundary docs
2) For each release-bar item A–E:
   - Determine PASS/FAIL/UNKNOWN
   - If FAIL/UNKNOWN:
     - Provide evidence: file path + function name + short excerpt description
     - Provide minimal reproducible example (LRL snippet or MIR snippet)
     - Suggest a minimal test that should exist to lock the behavior
3) Verify ignored tests:
   - Identify any `#[ignore]` tests related to soundness; list them explicitly and explain the risk
4) Run/inspect existing test corpus logic (no need to execute tools unless available):
   - Ensure key regressions are encoded as tests (Prop-elim, fix-in-total, deref aliasing, macro capture, alias->Unit lowering, Copy/closure duplication)

Output format (single Markdown report)
1) Executive verdict:
   - “GO for stdlib expansion” or “NO-GO”
   - Justify in 5–10 bullets
2) Release bar checklist table:
   - Each item A1–E16 marked PASS/FAIL/UNKNOWN
3) Blockers (must fix before stdlib):
   - List with evidence + minimal repro
4) High severity issues:
   - As above, but not necessarily blocking if mitigated and documented
5) Tests status:
   - Which soundness tests exist, which are missing, which are ignored
6) Suggested GitHub issues:
   - Title + severity + affected subsystem + acceptance criteria (test-based)

Rules
- Be concrete and evidence-based. No vague “should improve.”
- Do not propose new features; only evaluate against the existing intended policy.
- Do not implement fixes or refactors; only identify and justify.
- Treat “spec drift” as FAIL if it concerns semantics, or MEDIUM if only documentation is outdated.