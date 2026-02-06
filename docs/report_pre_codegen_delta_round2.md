# Pre-Codegen Review Delta (Round 2)

This delta report captures issues not called out in the initial review. It focuses on kernel/frontend/mir/cli pre‑codegen only.

## New / Missed Findings

### 1) Definitional equality can silently degrade to “false” on fuel exhaustion
**Location:** `kernel/src/checker.rs` `is_def_eq` (wraps `is_def_eq_result(...).unwrap_or(false)`).  
**Why it matters:** If defeq runs out of fuel, the result is treated as “not equal” instead of an error. This can cause type errors that appear as mismatch rather than “defeq fuel exhausted,” and it can vary with `LRL_DEFEQ_FUEL`.  
**Industrial alternative:** Make defeq fuel exhaustion a hard error in type checking paths, or at least propagate a diagnostic with context. Keep the “bool” helper only for tests.

### 2) Panic-free linter forbids all references, not just borrow_* primitives
**Location:** `mir/src/lints.rs` (`Statement::Assign(_, Rvalue::Ref(_, _))` check).  
**Why it matters:** The error message claims “borrow_shared/borrow_mut is forbidden,” but the implementation rejects *all* reference creation. This is stricter than intended and likely blocks valid programs.  
**Industrial alternative:** Track the origin of `Rvalue::Ref` (borrow_* vs other) or lint on specific primitives earlier in lowering. Update message/behavior to match policy.

### 3) Runtime check emission scans whole CFG per local (quadratic risk)
**Location:** `mir/src/analysis/nll.rs` `collect_runtime_checks_for_type`.  
**Why it matters:** For each local with interior mutability, it scans all statements/terminators to find uses. For large bodies with many locals, this is O(L * S).  
**Industrial alternative:** Precompute a use‑map once (local → locations) and reuse it for runtime check emission.

### 4) `panic_free` profile is applied late and only after NLL passes
**Location:** `cli/src/driver.rs` (panic_free lints after NLL).  
**Why it matters:** Programs that should be rejected earlier for panic‑free policy still run full MIR analysis. This wastes cycles and can mask “panic‑free” as a late lint rather than a compile mode.  
**Industrial alternative:** Treat panic‑free profile as a compile mode with early checks and explicit diagnostics, ideally before expensive analyses.

### 5) Borrow checker (lexical) and NLL both exist without explicit gating
**Location:** `mir/src/analysis/borrow.rs` vs `mir/src/analysis/nll.rs` usage in `cli/src/driver.rs`.  
**Why it matters:** Only NLL is used in the driver, but lexical borrow checker remains live and may drift. This increases maintenance surface and can cause conflicting diagnostics if accidentally wired.  
**Industrial alternative:** Feature‑gate or remove lexical checker, or make its use explicit behind a flag.

### 6) Macro boundary diagnostics depend on expansion trace order, but trace stack can include stale entries on errors
**Location:** `frontend/src/macro_expander.rs` `expansion_trace` and error paths.  
**Why it matters:** Some error paths return early without popping trace entries, which can lead to misleading macro expansion labels in later diagnostics.  
**Industrial alternative:** Use a scoped guard for trace push/pop or ensure trace is always unwound on error.

### 7) Determinism gap: constructor name lookup still relies on HashMap traversal
**Location:** `frontend/src/elaborator.rs` `resolve_name` (constructor search over `self.env.inductives`).  
**Why it matters:** This is distinct from the earlier “ambiguous constructor” issue: even without ambiguity, iteration order can affect which constructor is found first when multiple inductives have same ctor name (current behavior is “first match wins”).  
**Industrial alternative:** Explicit constructor index map with ambiguity checks.

### 8) Missing “panic‑free” profile definition at the kernel boundary
**Location:** `kernel/src/checker.rs` effect tracking + `cli/src/driver.rs` panic‑free lint.  
**Why it matters:** The policy is enforced only in MIR, not in kernel or elaboration, so the trusted kernel boundary does not “know” the profile. This makes it difficult to reason about panics in typed programs.  
**Industrial alternative:** Introduce an explicit profile flag passed from CLI → kernel/elaborator → MIR so both kernel checks and MIR lints can enforce the same policy.

## Updated Top Priority (Delta)
1. Defeq fuel exhaustion must be surfaced as a diagnostic, not coerced to “false.”  
2. Fix panic‑free linter semantics (don’t ban all references).  
3. Make runtime check emission sub‑quadratic by precomputing local uses.  

## Suggested Work Items (Delta)
1. Replace `is_def_eq` usage in typing paths with `is_def_eq_result` or structured errors.  
2. Split panic‑free lint into “forbid borrow_*” vs “forbid references,” and align diagnostics with actual policy.  
3. Add local‑use indexing for runtime check insertion.  
4. Add scoped guard for macro expansion trace to prevent stale entries.

