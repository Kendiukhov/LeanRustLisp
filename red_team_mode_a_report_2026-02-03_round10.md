# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 10

## Executive summary
- **Good progress:** lifetime labels are now structural in core terms, macro-boundary is `Deny` for the prelude, and function-kind docs align with `Fn/FnMut/FnOnce`. (README.md; `kernel/src/ast.rs`; `cli/src/compiler.rs`; `docs/spec/core_calculus.md`)
- **Blocker:** MIR type lowering erases non-inductive/alias types to `Unit`, and `Unit` is treated as `Copy`. This can silently bypass ownership/borrow enforcement for alias types (e.g., a `Ref Mut` type alias becomes `Unit`). (`mir/src/lower.rs` `lower_type_general` + `push_local`; `mir/src/types.rs`)
- **Contract violation:** hygiene model in spec promises macro-introduced identifiers do *not* capture call-site binders, but resolver accepts subset-scopes, so macro-introduced names can bind to caller variables. (`docs/spec/macro_system.md`; `frontend/src/desugar.rs`)
- **Contract violation / semantic gap:** effects are described as type-level (`Comp`), but the kernel only blocks partial defs syntactically; no effect type is enforced. (`README.md`; `kernel/src/checker.rs`)
- **TCB risk:** macro boundary only flags *tagged* axioms; untagged axioms can be macro-injected into the prelude even under `Deny`. (`frontend/src/macro_expander.rs`)
- **Defeq remains fuel-bounded**, so transparent unfolding can still reject valid programs (semantic DoS). (`kernel/src/nbe.rs`; `kernel/src/checker.rs`)
- **Per request:** this round does not revisit the “import classical placeholder axiom gap.”

## Contract violations
1. **Macro hygiene promise vs. resolver behavior (capture is possible).**
   - Spec says macro-introduced identifiers should not capture call-site bindings. (`docs/spec/macro_system.md` L36–59)
   - Resolver accepts subset-scope matches, so a macro-introduced `x` with extra scope can still resolve to a call-site `x`. (`frontend/src/desugar.rs` `scopes_compatible` + `resolve_binding`, L23–67)
   - This contradicts README’s “hygienic macros” goal. (`README.md` L50–51)

2. **Effect system promised in types, not enforced.**
   - README states partial defs live under an effect like `Comp`. (`README.md` L25–27, L52–53)
   - Kernel only enforces a syntactic “no partial in total” rule; it does not require `Comp` or any effect in the type. (`kernel/src/checker.rs` `check_effects`, L5142–5196)

3. **Rust‑grade resource discipline undermined by MIR type erasure of aliases.**
   - MIR lowering erases any non‑inductive/unknown type to `Unit` (including `Const` aliases). (`mir/src/lower.rs` `lower_type_general`, L291–319)
   - `Unit` is `Copy`, and `push_local`/`push_temp_local` upgrades `is_copy` based on MIR type. (`mir/src/types.rs` L600–608; `mir/src/lower.rs` L878–917)
   - This violates the README’s promise that safe code cannot create aliasing or use‑after‑move. (`README.md` L49–50)

## Soundness / TCB risks
- **Alias-type erasure → borrow/ownership bypass (High).**
  - Any definitional type alias (e.g., `MyRef := Ref Mut Nat`) is lowered as `Term::Const` and becomes `MirType::Unit`.
  - `Unit` is `Copy`, so MIR may copy values that are non‑copy in the kernel, enabling `&mut` aliasing in safe code.
  - Evidence: `mir/src/lower.rs` `lower_type_general` (L291–319), `push_local`/`push_temp_local` (L878–917), `mir/src/types.rs` `MirType::is_copy` (L600–608).

- **Macro boundary does not block untagged axioms (High/Med).**
  - Boundary only checks `axiom` *tags* (`classical`/`unsafe`), not plain axioms. (`frontend/src/macro_expander.rs` L486–519)
  - A macro can expand to `(axiom foo ...)` inside the prelude even with `MacroBoundaryPolicy::Deny`, silently expanding the TCB.

- **Defeq fuel is still a semantic DoS (Medium).**
  - Default fuel remains finite; large transparent unfolding can reject valid programs. (`kernel/src/nbe.rs` L1003–1092; `kernel/src/checker.rs` L2977–3061)

## Semantic gaps (severity)
- **[High] Effect system is not type-level.** Partial defs are not required to return `Comp` (or any effect), contrary to the stated design.
- **[High] Macro hygiene is not enforced.** The resolver allows capture of call-site bindings by macro-introduced identifiers.
- **[High] MIR type erasure of aliases.** Non‑inductive/alias types are lowered to `Unit`, bypassing ownership/borrow checks.
- **[Medium] Defeq fuel DoS.** Transparent unfolding plus bounded fuel can reject otherwise valid proofs/types.

## Minimal reproducible examples
1. **Macro hygiene capture (should be rejected or unbound, but likely captures):**
```lisp
(defmacro m () x)

(def test (pi x Nat Nat)
  (lam x Nat (m)))
```
Expected hygienic behavior: `(m)` should *not* bind to the caller’s `x`. Current resolver accepts subset-scopes. (`frontend/src/desugar.rs` L23–67; `docs/spec/macro_system.md` L36–59)

2. **Alias‑type erasure → `Unit` (ownership/borrow bypass):**
```lisp
(def MyRef (sort 1) (Ref Mut Nat))

(def id (pi r MyRef MyRef)
  (lam r MyRef r))

(def demo (pi x Nat Nat)
  (lam x Nat
    (let r MyRef (borrow_mut x)
      (let _ MyRef (id r)
        x))))
```
Kernel sees `MyRef` ≡ `Ref Mut Nat`, but MIR lowers `MyRef` to `Unit`, making it `Copy` and removing borrow constraints. (`mir/src/lower.rs` L291–319; `mir/src/types.rs` L600–608)

3. **Macro smuggling an untagged axiom into the prelude (macro boundary miss):**
```lisp
(defmacro smuggle () (axiom hidden (pi P Prop P)))
(smuggle)
```
Boundary only checks tagged axioms; this bypasses `MacroBoundaryPolicy::Deny`. (`frontend/src/macro_expander.rs` L486–519)

4. **Defeq fuel exhaustion (semantic DoS):**
```lisp
(def expand (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ m) (add (expand m) (expand m))))))
```
Type checking can exhaust defeq fuel on large inputs. (`kernel/src/nbe.rs` L1003–1092)

## Fix plan (prioritized)
1. **Lower types via WHNF before MIR erasure.**
   - **Where:** `mir/src/lower.rs` (`lower_type_general`, `lower_type_in_fn`).
   - **What:** `whnf_in_ctx` the type to unfold transparent aliases before matching on `Ind/Ref`.
   - **Why:** prevents alias types from collapsing to `Unit`.
   - **Tests:** alias of `Ref Mut` remains `MirType::Ref` (MIR snapshot); borrow checker rejects aliasing.

2. **Stop upgrading `is_copy` from erased MIR types.**
   - **Where:** `mir/src/lower.rs` (`push_local`, `push_temp_local`).
   - **What:** only set `is_copy = true` if kernel says Copy *or* MIR type is known safe copy *and* not derived from erasure.
   - **Why:** avoids “Unit makes everything Copy.”
   - **Tests:** alias to `Ref Mut` does not become Copy in MIR locals.

3. **Introduce `MirType::Erased` (or `Opaque`) to distinguish proof‑erasure from unknown types.**
   - **Where:** `mir/src/types.rs`, `mir/src/lower.rs`, `mir/src/analysis/*`.
   - **Why:** unknown runtime types should be treated as non‑Copy and borrow‑checked conservatively.
   - **Tests:** unknown types are non‑Copy; moves are enforced.

4. **Hygiene resolver: tighten scope compatibility.**
   - **Where:** `frontend/src/desugar.rs` `scopes_compatible`/`resolve_binding`.
   - **What:** require exact match or explicit “macro scopes must match” logic, not subset.
   - **Why:** prevent macro‑introduced capture.
   - **Tests:** spec example `(defmacro m () x)` does **not** capture caller `x`.

5. **Macro boundary: flag any `axiom` in macro output.**
   - **Where:** `frontend/src/macro_expander.rs` `collect_macro_boundary_hits_in_list`.
   - **What:** add `MacroBoundaryKind::Axiom` and trigger on any `(axiom ...)`.
   - **Why:** prevent TCB expansion via macros (especially prelude).
   - **Tests:** untagged axiom from macro is rejected under `Deny`.

6. **Effect typing enforcement for partial defs.**
   - **Where:** `kernel/src/checker.rs` `check_effects`; elaborator surface checks.
   - **What:** require `partial def` return type to be `Comp A` (or similar), or introduce explicit effect tracking.
   - **Why:** align with README promise and prevent silent effect leaks.
   - **Tests:** `partial def` returning `Nat` is rejected unless wrapped in `Comp`.

7. **Document current effect policy if full effect system is deferred.**
   - **Where:** `README.md`, `docs/spec/phase_boundaries.md`.
   - **Why:** eliminate spec/impl mismatch if effect typing isn’t implemented yet.

8. **Add MIR regression tests for alias lowering.**
   - **Where:** `mir/tests` or `cli/tests` snapshot.
   - **What:** compile a type alias to `Ref Mut` and ensure MIR has `Ref` + non‑Copy locals.

9. **Add hygiene regression tests.**
   - **Where:** `frontend/tests` (macro expansion snapshots).
   - **What:** the spec example should not capture; verify symbol resolution.

10. **Defeq fuel tuning hooks.**
    - **Where:** `kernel/src/nbe.rs`, CLI docs.
    - **What:** add `--defeq-fuel` guidance in diagnostics and maybe per‑definition `opaque` defaults for large recursors.
    - **Tests:** ensure actionable diagnostic with source of fuel policy.

11. **Audit lowering for `Const` in types.**
    - **Where:** `mir/src/lower.rs`.
    - **What:** handle `Term::Const` by looking up transparent defs and lowering their WHNF.

12. **Borrow‑checker coverage for erased types.**
    - **Where:** `mir/src/analysis/nll.rs` and `mir/src/analysis/ownership.rs`.
    - **What:** treat `Erased/Opaque` as non‑Copy and disallow moves unless explicit unsafe.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Macro hygiene fixed (macro‑introduced identifiers do not capture).
- [ ] MIR lowering resolves type aliases before erasure; no `Unit` for runtime types.
- [ ] `Unit` no longer forces `is_copy` for erased/unknown types.
- [ ] Macro boundary blocks *all* axioms from macros in prelude unless allowlisted.
- [ ] Partial defs are effect‑typed or docs updated to match current reality.
- [ ] Defeq fuel DoS is documented with mitigation path.

## Suggested GitHub issues (titles + labels)
- **“MIR lowering erases type aliases to Unit; &mut aliasing can slip through”** — labels: bug, soundness, mir
- **“Macro hygiene capture: scopes_compatible allows subset matches”** — labels: bug, soundness, frontend
- **“Macro boundary ignores untagged axioms”** — labels: bug, tcb, frontend
- **“Partial defs not effect‑typed (Comp) despite spec”** — labels: design, docs, kernel
- **“Defeq fuel DoS: provide mitigation and tests”** — labels: design, kernel, test
