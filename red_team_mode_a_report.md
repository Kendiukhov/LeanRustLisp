**Executive Summary**
- The kernel has concrete machinery for defeq via NbE and basic termination/positivity checks, which aligns with the “Lean-grade specification” goal (`kernel/src/nbe.rs:625`, `kernel/src/checker.rs:295`, `kernel/src/checker.rs:2025`).  
- The kernel boundary promised in the README is not enforced in the pipeline: the elaborator builds and types critical constructs (match/rec) without a kernel re-check, and the CLI trusts those results directly (`README.md:9`, `README.md:32`, `frontend/src/elaborator.rs:417`, `cli/src/driver.rs:109`).  
- Proof erasure and Prop restrictions are not enforced in practice: Prop-elim tests are ignored, and match elaboration allows Prop-to-Type computation (`kernel/tests/negative_tests.rs:290`, `frontend/src/elaborator.rs:420`).  
- Macro hygiene is broken for quasiquote-generated identifiers, violating the hygienic macro contract (`README.md:13`, `frontend/src/macro_expander.rs:135`).  
- The borrow checker and NLL analysis do not model deref aliasing, so “Rust-grade resource discipline” is not met (`README.md:11`, `mir/src/analysis/borrow.rs:80`, `mir/src/analysis/nll.rs:562`).  
- Definitional equality is fully transparent by default with no surface-level opaque control, and the elaborator uses `Transparency::All`, making defeq a potential DoS and undermining intended opacity (`kernel/src/ast.rs:65`, `frontend/src/declaration_parser.rs:50`, `frontend/src/elaborator.rs:135`).

**Stop-The-Line**
- Blocker: Match elaboration does not type-check case bodies against the motive; ill-typed matches are accepted (`frontend/src/elaborator.rs:609`).  
- Blocker: Prop elimination restrictions are bypassed via match elaboration; proofs can compute data, violating proof erasure (`frontend/src/elaborator.rs:420`, `kernel/tests/negative_tests.rs:290`).  
- Blocker: Borrow checking ignores deref aliasing; shared loans do not conflict with `*r` writes (`mir/src/analysis/borrow.rs:80`, `mir/src/analysis/nll.rs:562`).  
- Blocker: Indexed recursor reduction uses dummy indices; definitional equality is wrong for indexed inductives (`kernel/src/nbe.rs:781`).

**Contract Violations**
- “Small trusted kernel… everything else… outside the trust boundary” is violated: elaborator constructs recursor applications and assigns types without kernel validation, and the CLI accepts those results directly (`README.md:32`, `frontend/src/elaborator.rs:420`, `cli/src/driver.rs:109`).  
- “Rust-grade resource discipline” is violated: borrow/NLL conflict checks only compare `place.local`, so deref aliasing is unchecked (`README.md:11`, `mir/src/analysis/borrow.rs:80`, `mir/src/analysis/nll.rs:562`).  
- “Hygienic macros” is violated: quasiquote expansion injects `cons/append/quote` with empty scopes, allowing capture by caller bindings (`README.md:13`, `frontend/src/macro_expander.rs:135`).  
- “Proof erasure” is not enforced: Prop-elimination restriction tests are ignored and there is no enforced guard in match elaboration (`README.md:12`, `kernel/tests/negative_tests.rs:290`, `frontend/src/elaborator.rs:420`).  
- The “unsafe def” fragment is promised but not exposed in the surface syntax; only `def` and `partial` are parsed (`README.md:27`, `frontend/src/declaration_parser.rs:50`).

**Soundness/TCB Risks**
- **Kernel soundness risks**  
- Recursor reduction for indexed inductives uses dummy indices, so defeq can reduce to ill-typed terms (`kernel/src/nbe.rs:736`).  
- NbE `quote` erases lambda domain types (`Prop`), so `whnf` is not type-preserving; this can mislead any component using `whnf` as a typed normalizer (`kernel/src/nbe.rs:860`).  
- Partial/unsafe separation is enforced only at `Env::add_definition`, not in kernel inference; the kernel itself does not reject partials in type positions (`kernel/src/checker.rs:170`, `kernel/src/checker.rs:1984`).  

- **Compiler correctness risks**  
- Elaborator uses `Transparency::All` for whnf/defeq and unification; opaque definitions and defeq performance boundaries are ignored in elaboration (`frontend/src/elaborator.rs:135`, `frontend/src/elaborator.rs:757`).  
- Match elaboration ignores case-body typing, returning `ret_type_elab` unconditionally (`frontend/src/elaborator.rs:442`, `frontend/src/elaborator.rs:609`).  
- `build_recursor_type` and `build_minor_premise_type` are placeholders; direct `rec` use can be ill-typed (`frontend/src/elaborator.rs:370`).  
- The CLI does not re-run kernel type checking on elaborated terms before registering definitions (`cli/src/driver.rs:109`).

**Semantic Gaps (Severity)**
- [BLOCKER] Match case bodies are not checked against the motive; ill-typed matches are accepted (`frontend/src/elaborator.rs:609`).  
- [BLOCKER] Prop elimination restriction is bypassed by match elaboration; proof-to-data computation is possible (`frontend/src/elaborator.rs:420`, `kernel/tests/negative_tests.rs:290`).  
- [BLOCKER] Borrow/NLL analyses do not treat deref as aliasing the referent; aliasing violations slip through (`mir/src/analysis/borrow.rs:80`, `mir/src/analysis/nll.rs:562`).  
- [HIGH] Recursor reduction uses dummy indices; defeq is wrong for indexed inductives (`kernel/src/nbe.rs:781`).  
- [HIGH] No surface-level `opaque` control; defeq unfolding is fully transparent by default (`kernel/src/ast.rs:65`, `frontend/src/declaration_parser.rs:50`).  
- [MED] Classical axiom tracking is declared but not implemented (test ignored, no user reporting) (`kernel/tests/semantic_tests.rs:368`).  
- [MED] Unsafe fragment exists in kernel types but has no surface syntax or pipeline support (`kernel/src/ast.rs:125`, `frontend/src/declaration_parser.rs:50`).

**Minimal Reproducible Examples**
- **Repro 1 (Blocker: ill-typed match accepted)** — Elaborator does not check case bodies. (`frontend/src/elaborator.rs:609`)  
```lrl
(def bad_match (pi b Bool Nat)
  (lam b Bool
    (match b Nat
      (case (true) false)
      (case (false) true))))
```
Expected: reject (case bodies are Bool, motive is Nat).  
Observed risk: accepted, type assigned as Nat.

- **Repro 2 (Blocker: Prop → Type elimination)** — proof-to-data via `Eq`. (`frontend/src/elaborator.rs:420`, `kernel/tests/negative_tests.rs:290`)  
```lrl
(def proof_to_nat
  (pi A (sort 1)
    (pi a A
      (pi b A
        (pi p (Eq A a b) Nat))))
  (lam A (sort 1)
    (lam a A
      (lam b A
        (lam p (Eq A a b)
          (match p Nat
            (case (refl A' a') (succ zero))))))))
```
Expected: reject large elimination from Prop.  
Observed risk: accepted, enabling proof-dependent computation.

- **Repro 3 (High: macro hygiene capture via quasiquote)** — macro-introduced `cons` is unscoped. (`frontend/src/macro_expander.rs:135`)  
```lrl
(defmacro mk (x) `(cons ,x nil))

(def capture (pi cons Nat (List Nat))
  (lam cons Nat
    (mk cons)))
```
Expected: `mk` should use list constructor `cons`, not local `cons`.  
Observed risk: quasiquote expands `cons` without macro scope, so it can capture caller bindings.

- **Repro 4 (Blocker: borrow checker aliasing)** — MIR-level example showing `*r` not checked against loan on `x`. (`mir/src/analysis/borrow.rs:80`, `mir/src/analysis/nll.rs:562`)  
```text
bb0:
  _1 = & _0        // shared loan of _0
  *_1 = 1          // write through deref
```
Expected: reject (write while shared-borrowed).  
Observed risk: `places_conflict` compares only locals, so `_1` vs `_0` does not conflict.

- **Repro 5 (High: defeq/perf blowup)** — transparent unfolding with no opaque escape. (`kernel/src/ast.rs:65`, `kernel/src/nbe.rs:640`)  
```lrl
(def boom (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ n' ih) (add ih ih)))))

(def boom_eq (pi n Nat (Eq Nat (boom n) (boom n)))
  (lam n Nat (refl Nat (boom n))))
```
Expected: defeq should not require full normalization or should allow `opaque` to avoid blowups.  
Observed risk: defeq normalization unfolds `boom` eagerly, causing exponential work.

- **Repro 6 (Classical axiom laundering visibility gap)** — no user-facing tracking. (`kernel/tests/semantic_tests.rs:368`)  
```lrl
(axiom classical_choice (pi A (sort 1) (pi p (pi x A (sort 0)) A)))
(def uses_classical (pi A (sort 1) A)
  (lam A (sort 1)
    (classical_choice A (lam x A (sort 0)))))
```
Expected: tool should flag `uses_classical` as classical.  
Observed risk: no pipeline reporting or enforcement.

**Fix Plan (Prioritized)**
- P1: What: add kernel recheck after elaboration (infer term, check against expected with `Transparency::Reducible`). Where: `cli/src/driver.rs:109`, new `kernel::checker::check` call. Why: shrink TCB to kernel. Tests: add failing match case test in `tests/` and ensure rejection.  
- P2: What: enforce motive/case typing in `elaborate_match` by checking each case body against the motive. Where: `frontend/src/elaborator.rs:609`. Why: prevent ill-typed matches. Tests: `bad_match` negative test.  
- P3: What: compute proper recursor levels from motive and call `check_elimination_restriction`; pass explicit levels in `Term::Rec`. Where: `frontend/src/elaborator.rs:420`, `kernel/src/checker.rs:1807`. Why: prevent Prop → Type elimination. Tests: unignore `negative_large_elim_from_prop` in `kernel/tests/negative_tests.rs:290`.  
- P4: What: implement `unsafe` surface syntax and propagate to `Definition::unsafe_def`. Where: `frontend/src/declaration_parser.rs:50`, `cli/src/driver.rs:150`. Why: honor README safety boundary. Tests: parser tests for `(unsafe ...)` and effect boundary checks.  
- P5: What: add `opaque`/`transparent` attributes in surface syntax and store in `Definition::transparency`; default to reducible but allow user escape. Where: `frontend/src/declaration_parser.rs:50`, `kernel/src/ast.rs:65`. Why: defeq/perf control. Tests: defeq test where opaque def does not unfold.  
- P6: What: use `Transparency::Reducible` (or user-chosen transparency) in elaborator whnf/defeq/unify. Where: `frontend/src/elaborator.rs:135`, `frontend/src/elaborator.rs:757`. Why: honor opacity and reduce TCB. Tests: opaque-def unification tests.  
- P7: What: fix `try_reduce_rec` to propagate actual indices into IH arguments instead of dummy `Sort 0`. Where: `kernel/src/nbe.rs:781`. Why: defeq correctness for indexed inductives. Tests: add indexed inductive (Eq/Vec) reduction tests.  
- P8: What: store lambda domain types in `Value::Lam` and preserve them in `quote`/`whnf`. Where: `kernel/src/nbe.rs:860`. Why: type-preserving normalization. Tests: `whnf` of lambda retains binder type.  
- P9: What: make borrow conflict detection projection-aware and deref-aliasing aware; treat `*r` as conflicting with loans on referent. Where: `mir/src/analysis/borrow.rs:80`, `mir/src/analysis/nll.rs:562`. Why: Rust-grade aliasing rules. Tests: MIR test that `*r` write under shared loan fails.  
- P10: What: implement projection-aware `place_type` and handle `Deref`/`Field` in NLL. Where: `mir/src/analysis/nll.rs:383`. Why: accurate region/loan tracking. Tests: NLL corpus covering deref, field, and reborrow.  
- P11: What: surface axiom dependency reporting (e.g., `:axioms` or error/warn on classical use). Where: `cli/src/driver.rs:165` plus metadata plumbing. Why: prevent axiom laundering. Tests: unignore `test_classical_axiom_tracking` in `kernel/tests/semantic_tests.rs:368`.  
- P12: What: add defeq fuel/memoization and detection of exponential unfolding; optionally warn on transparent defeq in types. Where: `kernel/src/nbe.rs:625`. Why: avoid defeq DoS. Tests: `boom_eq` should not time out (or should fail fast with diagnostic).  

**Go/No-Go Checklist (Stdlib Expansion)**
- Kernel re-check of elaborator output is in place for all `def`/`inductive`/`expr` pipelines (`cli/src/driver.rs:109`).  
- Match case typing and Prop elimination restrictions are enforced with non-ignored tests.  
- Borrow/NLL checks are deref/projection aware and have coverage for aliasing scenarios.  
- Indexed inductive recursor reduction is correct (no dummy indices).  
- Macro hygiene covers quasiquote-generated identifiers.  
- Opaque/transparent control is exposed and honored in elaboration and defeq.  
- Classical axiom dependencies are surfaced to users.

**Suggested GitHub Issues**
- “Elaborator accepts ill-typed match cases (motive unchecked)” — labels: bug/soundness/test.  
- “Prop elimination restriction bypassed via match elaboration” — labels: bug/soundness/test.  
- “Borrow/NLL ignore deref aliasing; loans tracked only by local” — labels: bug/soundness.  
- “Indexed recursor reduction uses dummy indices in NbE” — labels: bug/soundness/design.  
- “Expose `opaque`/`transparent` in surface syntax; honor in elaborator” — labels: design/soundness/test.  
- “Implement classical axiom dependency reporting; unignore test” — labels: design/docs/test.  
- “Macro hygiene: quasiquote-generated `cons/append/quote` not scoped” — labels: bug/soundness/test.
