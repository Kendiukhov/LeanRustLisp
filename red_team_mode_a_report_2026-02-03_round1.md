# Red Team Mode A Report (Semantic / Pre-Codegen) — 2026-02-03 Round 1

## Executive summary
- **Blocker: totality is unsound.** The termination checker accepts self-referential total defs when recursion is not syntactically an application (e.g., `def loop := loop` or via `let`), so total defs can diverge and defeq can loop/consume fuel. Evidence: termination pipeline in `kernel/src/checker.rs` (`check_termination_with_hint` around L800–855) relies on `contains_recursive_call` (L1265–1288) but `check_recursive_calls_ctx` treats bare `Const` as OK and only validates `extract_app_to_const` calls (L1312–1359), allowing non-terminating total defs.
- **Safe borrowing is currently unusable.** Surface `&`/`&mut` desugars to `borrow_shared`/`borrow_mut` (`frontend/src/desugar.rs` L592–623), but these are `unsafe` axioms (`stdlib/prelude.lrl` L23–28). `check_effects` forbids unsafe in Total/Partial (kernel/src/checker.rs L4360–4413). This contradicts README’s “safe code can’t create use-after-free” promise (README.md L40).
- **Shared refs Copy mismatch across phases.** Spec claims shared refs are Copy (`docs/spec/ownership_model.md` L25–30). MIR treats `&T` as Copy (`mir/src/types.rs` L591–596). Kernel `is_copy_type` treats only inductives/Sorts as Copy; `Ref` is an axiom, so `Ref Shared A` is non-Copy (`kernel/src/checker.rs` L2680–2724). This creates semantic inconsistency between kernel ownership and MIR assumptions.
- **Macro system allows shadowing core forms.** Only `opaque/transparent/import/eval` are reserved (`frontend/src/macro_expander.rs` L55–59), so macros can shadow `def`, `axiom`, `unsafe`, `partial`, etc. Expansion uses any non-reserved head symbol as a macro (`frontend/src/macro_expander.rs` L790–826). This undermines explicitness of unsafe/classical boundaries required by spec (`docs/spec/macro_system.md` L61–68, L126–130) and README’s “unsafe is explicit” stance (README.md L45).

## Stop-the-line list (prioritized)
1. **Termination checker hole** allows non-terminating total defs (kernel/src/checker.rs L800–855, L1265–1359). This is a kernel soundness blocker.
2. **Shared ref Copy mismatch** breaks ownership semantics across kernel/MIR (docs/spec/ownership_model.md L25–30, kernel/src/checker.rs L2680–2724, mir/src/types.rs L591–596).
3. **Borrowing primitives are unsafe-only** yet surface `&` desugars to them (frontend/src/desugar.rs L592–623; stdlib/prelude.lrl L23–28; kernel/src/checker.rs L4360–4413). Safe code cannot borrow; contradicts contract.

## Safe-to-proceed checklist (for stdlib expansion)
- [ ] Termination checker rejects non-application self-recursion and indirect self-reference (kernel/src/checker.rs termination path).
- [ ] Shared ref Copy semantics are aligned between kernel, spec, and MIR (docs/spec/ownership_model.md; kernel/src/checker.rs; mir/src/types.rs).
- [ ] Borrowing primitives are safe or the surface syntax requires explicit `unsafe` (frontend/src/desugar.rs; stdlib/prelude.lrl; kernel/src/checker.rs).
- [ ] Core forms cannot be macro-shadowed (frontend/src/macro_expander.rs).

## Contract violations
1. **Termination enforcement is not actually enforced for total defs.** Spec says kernel enforces termination (docs/spec/kernel_boundary.md L10–18), but `check_termination_with_hint` accepts recursion that is a bare constant or hidden behind `let` because `check_recursive_calls_ctx` only validates applications (`extract_app_to_const`) and treats `Const` as OK (kernel/src/checker.rs L800–855, L1265–1359, L1522–1535). This violates the “total fragment” contract.
2. **Safe borrowing is not available in safe code.** README promises safe borrowing prevents UAF/data races (README.md L40), but surface `&`/`&mut` desugars to `borrow_shared`/`borrow_mut` (frontend/src/desugar.rs L592–623), which are declared `unsafe` axioms in the prelude (stdlib/prelude.lrl L23–28) and are forbidden in Total/Partial by `check_effects` (kernel/src/checker.rs L4360–4413).
3. **Shared ref Copy contract is violated.** Spec: shared refs are Copy (docs/spec/ownership_model.md L25–30). MIR models `&T` as Copy (mir/src/types.rs L591–596). Kernel `is_copy_type` only recognizes inductives/Sorts as Copy, so `Ref Shared A` (an axiom) is treated non-Copy (kernel/src/checker.rs L2680–2724). This breaks the stated ownership model.
4. **Macro explicitness contract is weakened.** Spec says core attributes are reserved and classical/unsafe forms must be explicit in expanded syntax (docs/spec/macro_system.md L61–68, L126–130). The expander only reserves `opaque/transparent/import/eval` (frontend/src/macro_expander.rs L55–59) and allows macro expansion for any other head symbol (L790–826). This allows shadowing `def`/`axiom`/`unsafe`/`partial`, violating explicitness guarantees.

## Soundness / TCB risks
- **Kernel soundness risk:** Non-terminating total definitions can be admitted (kernel/src/checker.rs L800–855, L1265–1359). This makes definitional equality potentially diverge or hit fuel exhaustion for programs that should be total, expanding the trusted core beyond intended guarantees.
- **Cross-phase semantic mismatch risk:** Kernel ownership rules treat `Ref Shared` as linear while MIR assumes it is Copy (kernel/src/checker.rs L2680–2724 vs mir/src/types.rs L591–596). This can make “safe” MIR programs unrepresentable at the kernel level and risks inconsistent reasoning about aliasing.
- **Macro boundary risk (explicitness):** Macro shadowing of `def`/`axiom`/`unsafe`/`partial` enables classical/unsafe laundering at the source level (frontend/src/macro_expander.rs L55–59, L790–826). While kernel still tracks axioms, the user-facing explicitness contract is breached (docs/spec/macro_system.md L61–68, L126–130; README.md L45).

## Semantic gaps (with severity)
- **[Blocker] Termination validation misses non-application self-recursion.** See `check_recursive_calls_ctx` + `extract_app_to_const` (kernel/src/checker.rs L1312–1359, L1522–1535).
- **[High] Safe borrowing not expressible in safe fragment.** `&`/`&mut` desugar to unsafe axioms; safe code cannot borrow (frontend/src/desugar.rs L592–623; stdlib/prelude.lrl L23–28; kernel/src/checker.rs L4360–4413).
- **[High] Shared-ref Copy semantics inconsistent.** Spec + MIR say Copy; kernel says non-Copy (docs/spec/ownership_model.md L25–30; kernel/src/checker.rs L2680–2724; mir/src/types.rs L591–596).
- **[Medium] Macro forms can be shadowed.** Only 4 reserved names (frontend/src/macro_expander.rs L55–59), undermining explicit unsafe/classical boundaries (docs/spec/macro_system.md L61–68, L126–130).
- **[Medium] FnMut not implemented.** Spec reserves FnMut but not implemented (`docs/spec/function_kinds.md` L28–30). Closures with mutable capture are forced into FnOnce, which is overly restrictive and diverges from desired Rust-like semantics.

## Minimal reproducible examples
1. **Non-terminating total def accepted (bare self-reference):**
```lisp
(def loop (pi x Nat Nat)
  loop)
```
Expected: reject as non-terminating; actual: accepted because recursion is a bare `Const` and never validated as a call (kernel/src/checker.rs L1312–1359).

2. **Indirect recursion via `let` accepted:**
```lisp
(def loop (pi x Nat Nat)
  (let g (pi x Nat Nat) loop
    (g x)))
```
`contains_recursive_call` sees `loop`, but `check_recursive_calls_ctx` never validates the call since it’s via a `let` alias.

3. **Safe borrowing rejected (unsafe primitive under the hood):**
```lisp
(def safe_borrow (pi x Nat (Ref Shared Nat))
  (& x))
```
Fails because `&` desugars to `borrow_shared` (unsafe) and Total defs cannot call unsafe (frontend/src/desugar.rs L592–607; stdlib/prelude.lrl L23–28; kernel/src/checker.rs L4360–4413).

4. **Shared ref duplication rejected (should be Copy):**
```lisp
(def use_shared (pi r (Ref Shared Nat) Nat)
  (lam r (Ref Shared Nat) zero))

(unsafe dup_shared (pi x Nat Nat)
  (lam x Nat
    (let r (Ref Shared Nat) (& x)
      (let _ Nat (use_shared r)
        (use_shared r)))))
```
Spec says shared refs are Copy, but kernel treats `Ref` as non-Copy (kernel/src/checker.rs L2680–2724).

5. **Macro shadowing can hide unsafe/classical:**
```lisp
(defmacro def (name ty val) (unsafe def name ty val))
(def foo Nat zero) ;; expands to unsafe def without explicit unsafe in source

(defmacro axiom (name ty) (axiom classical name ty))
(axiom choice Prop) ;; classical in expansion, non-classical in source
```
Allowed because only `opaque/transparent/import/eval` are reserved (frontend/src/macro_expander.rs L55–59, L790–826).

## Fix plan (prioritized, 10–20 tasks)
1. **Reject bare self-reference in total defs.**
   - **What:** In termination checking, treat `Const def_name` occurring in the body (not under application) as a recursive call without arguments and reject unless a decreasing argument can be established. Alternatively, require that a function-typed total definition body is lambda-headed (eta-expand or error).
   - **Where:** `kernel/src/checker.rs` (`check_termination_with_hint`, `check_recursive_calls_ctx`, `peel_lambdas`, `contains_recursive_call`).
   - **Why:** Prevent non-terminating total defs.
   - **Tests:** Add negative tests in `kernel/tests/negative_tests.rs` for `def loop := loop` and `let`-aliased recursion.
2. **Ensure recursive calls are validated even via let-binding.**
   - **What:** Track aliases in termination ctx or treat `let`-bound constants matching def_name as recursive calls.
   - **Where:** `kernel/src/checker.rs` (`check_recursive_calls_ctx` on `LetE`).
   - **Why:** Close aliasing hole in termination.
   - **Tests:** `kernel/tests/negative_tests.rs` case for `let g = loop; g x`.
3. **Make borrow primitives safe in the total fragment (or require explicit unsafe at surface).**
   - **What:** Decide policy: either (a) reclassify `borrow_shared`/`borrow_mut` as Total primitives (remove `unsafe` tags), or (b) make `&`/`&mut` syntax require `unsafe` context explicitly.
   - **Where:** `stdlib/prelude.lrl`, `kernel/src/checker.rs::check_effects`, `frontend/src/desugar.rs`.
   - **Why:** Align with README’s safety guarantees and make borrowing usable.
   - **Tests:** `tests/pending/borrow_surface*.lrl` should move out of `unsafe` if safe, or compiler should error unless `unsafe` if policy (b).
4. **Introduce kernel-level Copy rule for shared refs.**
   - **What:** Add a builtin check in `is_copy_type` to treat `Ref Shared A` as Copy and `Ref Mut A` as non-Copy.
   - **Where:** `kernel/src/checker.rs` (`is_copy_type_inner`) plus a canonical way to identify `Ref/Shared/Mut` (e.g., env-known defs).
   - **Why:** Match spec + MIR semantics.
   - **Tests:** New kernel tests asserting Copy for `Ref Shared` and non-Copy for `Ref Mut`.
5. **Align MIR and kernel Copy semantics with spec.**
   - **What:** Add regression tests verifying shared ref duplication is accepted by kernel and MIR borrow checker remains sound.
   - **Where:** `kernel/tests/semantic_tests.rs`, `mir/tests/borrowck_corpus.rs`.
   - **Why:** Cross-phase consistency.
6. **Expand reserved macro names for core forms.**
   - **What:** Add `def`, `axiom`, `unsafe`, `partial`, `instance`, `inductive`, `structure` to `RESERVED_MACRO_NAMES`.
   - **Where:** `frontend/src/macro_expander.rs`.
   - **Why:** Prevent shadowing core forms and unsafe/classical laundering.
   - **Tests:** New frontend test asserting `(defmacro def ...)` is rejected.
7. **Add lints/warnings for macros that emit unsafe/classical forms.**
   - **What:** When macro expansion emits `unsafe` or `axiom classical`, emit a diagnostic at call site.
   - **Where:** `frontend/src/macro_expander.rs` or declaration parser.
   - **Why:** Preserve explicitness even with macros.
   - **Tests:** `frontend/tests` macro expansion diagnostics.
8. **FnMut introduction (per roadmap).**
   - **What:** Add `FnMut` to `FunctionKind`, update parser/desugar, elaborator, and ownership inference to classify mutable captures as `FnMut`, not `FnOnce`.
   - **Where:** `kernel/src/ast.rs`, `kernel/src/checker.rs`, `frontend/src/desugar.rs`, `frontend/src/elaborator.rs`, docs/spec/function_kinds.md.
   - **Why:** Align closure semantics with Rust-like behavior and reduce unnecessary FnOnce restrictions.
   - **Tests:** Add elaborator tests for mutable captures and function-kind coercions.
9. **Improve defeq error reporting for fuel exhaustion.**
   - **What:** Surface context + definition name when `DefEqFuelExhausted` arises.
   - **Where:** `kernel/src/checker.rs` error mapping.
   - **Why:** Aid diagnostics for large transparent definitions.
10. **Add regression test for defeq on non-terminating total defs.**
    - **What:** Ensure defeq rejects or errors on a total def that would diverge (after fix, should not be admitted).
    - **Where:** `kernel/tests/defeq_budget_tests.rs` or `kernel/tests/negative_tests.rs`.
    - **Why:** Prevent regressions in termination/defeq interplay.
11. **Document borrowing policy explicitly.**
    - **What:** Update `docs/spec/ownership_model.md` and `docs/spec/kernel_boundary.md` to match actual borrow primitive status and safety rules.
    - **Where:** docs.
    - **Why:** Avoid contract drift.
12. **Add macro-system spec compliance tests.**
    - **What:** Ensure reserved forms and attributes cannot be shadowed.
    - **Where:** `frontend/tests`.
    - **Why:** Enforce explicitness/hygiene contract.

## Go / No-Go checklist for stdlib expansion
- [ ] Termination checker soundness hole closed (bare/self recursion and aliasing blocked).
- [ ] Borrowing available in safe code or surface syntax requires explicit `unsafe`.
- [ ] Shared ref Copy semantics aligned across spec, kernel, MIR.
- [ ] Core forms are macro-reserved to preserve explicitness.
- [ ] FnMut plan either implemented or explicitly excluded and documented.

## Suggested GitHub issues (titles + labels)
- **“Termination checker misses non-application self-recursion in total defs”** — labels: bug, soundness, kernel.
- **“Borrow primitives are unsafe-only; surface & is unusable in safe code”** — labels: bug, design, frontend, kernel.
- **“Shared reference Copy semantics mismatch (spec vs kernel vs MIR)”** — labels: bug, soundness, mir, kernel.
- **“Macro expander allows shadowing core forms (def/axiom/unsafe/partial)”** — labels: bug, design, frontend.
- **“Implement FnMut function kind and mutable-capture inference”** — labels: design, frontend, kernel.

