# Red Team Core Report (P1–P8)

Date: 2026-02-06
Mode: Pre-codegen release-bar audit (scope-limited to P1–P8)
Repository: LeanRustLisp

## 1) Executive Verdict
**NO-GO** for stdlib expansion under P1–P8.

Rationale: I found stop-the-line bypasses where MIR/NLL and interior-mutability gate diagnostics are emitted, but the offending definitions remain admitted and can still be referenced/executed in the default file/interpreter path.

## 2) Checklist (P1–P8)

| Promise | Status | Notes |
|---|---|---|
| P1 Kernel boundary enforced | PASS | Top-level defs/exprs are kernel re-checked before admission/eval in driver path. |
| P2 Totality boundary enforced | PASS | `fix` rejected outside `partial`; `partial` requires `Comp` return; partial-in-type blocked. |
| P3 Prop/erasure safety | UNKNOWN | Kernel checks are strong; however docs/policy vs MIR Prop-classification behavior around `opaque` in erasure is inconsistent and needs explicit lock-in test. |
| P4 Macro boundary + hygiene (current policy) | PASS | Deny policy is enforced post-expansion (incl. quasiquote); hygiene tests pass for current documented behavior. |
| P5 Borrow/lifetime safety via MIR/NLL non-bypassable | FAIL | NLL errors are non-fatal in interpreter/file execution path; rejected defs still usable. |
| P6 Axiom/noncomputable policy explicit + enforced | PASS | Kernel tags + dependency tracking + noncomputable gating present; strict tag mode covered. |
| P7 Interior mutability policy enforced | FAIL | Gate emits error but definition is still left in env (safe-mode rejection is not transactional). |
| P8 Defeq fuel/transparency no silent bypass | PASS | Fuel exhaustion/fix-unfold become explicit diagnostics; no success-on-exhaustion in typechecking path. |

## 3) Stop-The-Line Blockers (max 5)

### B1) P5 bypass: MIR/NLL borrow failures do not prevent execution in file/interpreter mode
**Severity:** Stop-the-line

**Evidence citations**
- `cli/src/driver.rs:948` (definition admitted to `Env` before MIR/NLL safety phase)
- `cli/src/driver.rs:1078` (NLL check runs)
- `cli/src/driver.rs:1092` (NLL errors only appended as diagnostics)
- `cli/src/driver.rs:1752` (expressions continue processing)
- `cli/src/driver.rs:1867` (expression evaluation still runs)
- `cli/src/repl.rs:354` (file mode uses `process_code` and prints diagnostics, no rollback)
- `cli/src/main.rs:209` (default `cli <file>` path uses `repl::run_file`)

**Minimal repro**
File (`/tmp/p5_bypass_transitive.lrl`):
```lrl
(noncomputable use_shared (pi r (Ref #[r] Shared Nat) Nat)
  (lam r (Ref #[r] Shared Nat) zero))

(noncomputable use_mut (pi r (Ref #[r] Mut Nat) Nat)
  (lam r (Ref #[r] Mut Nat) zero))

(noncomputable borrow_then_mutate (pi x Nat Nat)
  (lam x Nat
    (let r (Ref #[r] Shared Nat) (& x)
      (let m (Ref #[r] Mut Nat) (&mut x)
        (use_shared r)))))

(def use_bad Nat (borrow_then_mutate zero))
use_bad
```
Command:
```bash
cargo run -p cli -- /tmp/p5_bypass_transitive.lrl
```

**Observed**
- Emits `[M200] Borrow error in borrow_then_mutate ...`
- Still emits `Eval: Ctor("Nat", 0, [])` for `use_bad`
- `use_bad` is admitted and referenced despite upstream borrow failure.

**Expected**
- Any MIR/NLL safety failure should reject the offending definition from the admitted environment for that run.
- Dependent definitions/expressions should fail with unknown symbol or prior-hard-failure semantics.

**Smallest fix direction**
- Make definition admission transactional with MIR/NLL:
1. Build + kernel-check core term.
2. Run MIR typing/ownership/NLL.
3. Only then commit definition into `Env`.
- Or: if def already inserted, rollback/remove on any MIR/NLL error before processing subsequent declarations/expressions.

**Required regression test**
- New CLI integration test: after a borrow-error definition, a later declaration/expression referencing it must fail (no eval output, no successful deployment of dependents).

---

### B2) P7 bypass: interior-mutability safe-mode gate is diagnostic-only (non-transactional)
**Severity:** Stop-the-line

**Evidence citations**
- `cli/src/driver.rs:966` (gate check after successful `env.add_definition`)
- `cli/src/driver.rs:974` (C0005 diagnostic emitted)
- `cli/src/driver.rs:979` (`continue` without removing admitted definition)

**Minimal repro**
File (`/tmp/p7_bypass_repl.lrl`):
```lrl
(noncomputable uses_refcell (pi x (RefCell Nat) Nat)
  (lam x (RefCell Nat) zero))

(uses_refcell (mk_refcell zero))
```
Command:
```bash
cargo run -p cli -- /tmp/p7_bypass_repl.lrl
```

**Observed**
- Emits C0005: interior mutability gated.
- Subsequent expression resolves `uses_refcell` (not unknown), then gets C0004 eval-blocked due axiom dependency.
- This proves gated definition stayed admitted.

**Expected**
- In safe mode (`--allow-axioms` off), gated interior-mutability definitions should be rejected, not retained.

**Smallest fix direction**
- When C0005 is triggered, remove/rollback the just-admitted definition and avoid adding it to `deployed_definitions`.

**Required regression test**
- New test: with `allow_axioms=false`, defining `uses_refcell` must make subsequent references fail as undefined in the same processing unit.

## 4) Non-Blocking Issues (within P1–P8)

1. **P3 policy drift risk (`opaque` + Prop erasure classification):**
   - Contract says Prop classification respects `opaque` by default, with explicit opt-in contexts.
   - `mir/src/lower.rs:1479` currently calls `is_prop_like_with_transparency(..., PropTransparencyContext::UnfoldOpaque)` for local `is_prop` marking used by erasure.
   - Docs and behavior should be explicitly aligned with a regression test (either code or docs).

## 5) Suggested GitHub Issues (title + labels + acceptance test)

1. **Title:** Make MIR/NLL safety failures transactional in `process_code`
   - Labels: `release-bar`, `soundness`, `borrowck`, `cli-driver`, `P5`
   - Acceptance test: a file with a known borrow error followed by dependent decl/expr must not evaluate and dependent symbol resolution must fail.

2. **Title:** Roll back interior-mutability-gated definitions when `--allow-axioms` is off
   - Labels: `release-bar`, `safety-policy`, `cli-driver`, `P7`
   - Acceptance test: after gated RefCell/Mutex definition in safe mode, same-run reference reports undefined symbol (not only eval-blocked).

3. **Title:** Lock `opaque` Prop-classification behavior for MIR erasure with policy test
   - Labels: `spec-alignment`, `erasure`, `kernel-mir-boundary`, `P3`
   - Acceptance test: add a targeted test proving whether opaque Prop aliases are or are not unfolded for erasure, and keep docs consistent with that result.

## Evidence Run Log (executed)
- `cargo test -p cli pipeline_negative -- --nocapture` (passed)
- `cargo test -p kernel --test readme_promises_tests -- --nocapture` (passed)
- `cargo test -p frontend macro -- --nocapture` (passed)
- `cargo test -p mir nll -- --nocapture` (passed)
- Manual CLI repros:
  - `cargo run -p cli -- /tmp/p5_bypass_repl.lrl`
  - `cargo run -p cli -- /tmp/p5_control_no_expr.lrl`
  - `cargo run -p cli -- /tmp/p5_bypass_transitive.lrl`
  - `cargo run -p cli -- /tmp/p7_bypass_repl.lrl`
