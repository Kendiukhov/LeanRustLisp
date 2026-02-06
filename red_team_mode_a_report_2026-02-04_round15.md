# Red Team Mode A Report (2026-02-04 Round 15)

**Executive Summary**
- The kernel currently enforces ownership/linearity and effect boundaries inside `Env::add_definition`, which contradicts the README’s “borrow checking is outside the trust boundary” claim and widens the TCB in practice.
- The environment allows redefinition of existing inductives/definitions (including prelude items like `Comp`/`Nat`) without any guard; this breaks the “prelude is trusted” contract and enables axiom/classical laundering via name reuse.
- NLL borrow checking models `Fn`/`FnMut` calls as ephemeral borrows but does not create loans or lifetime constraints tying returned references to the borrow-of-self; closures that return references to owned captures appear able to outlive the closure, a high-severity soundness risk.
- `opaque` is not a hard escape hatch: Prop-likeness checks and MIR borrow-shape inference unfold opaque definitions with `Transparency::All`, undermining the README’s “opaque stays folded” promise for typechecking/defeq predictability.
- Classical axiom tracking is implemented and mostly solid, but it is vulnerable to redefinition-based laundering because tag lookup is done at query time against the current environment.
- The Prop/large-elimination rules are stricter than Lean in places (safe but restrictive); not a soundness hole, but a semantic gap to document.
- Conclusion: **No-Go** for stdlib expansion until redefinition, closure-borrow, and opaque/TCB boundary issues are fixed or explicitly re-scoped.

**Contract Violations**
1. **Kernel does ownership/linearity checks despite README claiming borrow checking is outside TCB.** The kernel calls `check_ownership_in_term` during `Env::add_definition`, making ownership part of the trusted core. Evidence: `kernel/src/checker.rs:863-867` inside `add_definition`. This contradicts README “borrow checking … is outside the trust boundary.”
2. **Prelude is not protected; redefinition is allowed.** `Env::add_inductive` and `Env::add_definition` both insert placeholders into maps without rejecting existing entries, allowing user code to redefine prelude items (`Comp`, `Nat`, `Eq`, etc.) after they were trusted. Evidence: `kernel/src/checker.rs:676-707` (`add_inductive` uses `self.inductives.insert`), `kernel/src/checker.rs:772-836` (`add_definition` uses `self.definitions.insert`), with no duplicate-name guard.
3. **`opaque` is not respected during typechecking for Prop/borrow semantics.** `is_prop_like` normalizes with `Transparency::All`, which unfolds opaque definitions, and MIR lowering explicitly unfolds opaque definitions to recover borrow shapes. Evidence: `kernel/src/checker.rs:4080-4088` (`Transparency::All`), `mir/src/lower.rs:707-723` (`borrow_shape_unfold` uses `Transparency::All`). README states opaque stays folded during typechecking; this is a direct mismatch.

**Soundness / TCB Risks**
- **High: Closure call borrow does not constrain returned references.** `Fn`/`FnMut` call operands are represented as `CallOperand::Borrow` (`mir/src/lower.rs:1495-1516`), but NLL only creates loans for `Rvalue::Ref` assignments (`mir/src/analysis/nll.rs:567-588`). `call_operand_type` treats a borrow of a closure as the closure’s type, not a `&self` with a lifetime (`mir/src/analysis/nll.rs:1028-1032`), and `normalize_callable_type` discards closure self semantics (`mir/src/analysis/nll.rs:1116-1124`). This creates a plausible unsoundness: a closure that returns a reference to owned captured data can yield a reference that outlives the closure’s borrow, enabling use-after-free once the closure is dropped.
- **High: Redefinition enables axiom/classical laundering and invalidates previously-checked terms.** Because definitions/inductives can be overwritten without re-checking prior terms, any soundness or axiom-tag guarantees can be retroactively invalidated. `axiom_dependencies_with_tag` uses the current environment to classify tags (`kernel/src/checker.rs:5247-5263`), so redefining an axiom name to a non-classical def can erase classical dependency reports.
- **Medium: `opaque` is not a predictable performance escape hatch.** The Prop-likeness check (`is_prop_like`) always unfolds opaque definitions, and MIR borrow-shape detection also unfolds opaques. This can reintroduce defeq/perf cliffs through code paths the user expects to be opaque, undermining the README’s stated control knob for predictability.

**Semantic Gaps**
- **High: Closure self-borrow lifetime model is missing.** There is no explicit `&self` parameter in closure types, which means lifetime relationships between `self` and returned references are not expressible in MIR/NLL. This is a semantic hole for `Fn`/`FnMut` closures returning refs.
- **Medium: `opaque` semantics are underspecified.** The compiler ignores `opaque` for Prop checks and borrow-shape inference; this should be documented as a semantic exception or revised to honor `opaque` uniformly.
- **Medium: Prelude “trusted boundary” is not enforced at the name level.** Because redefinition is permitted, the trust model is effectively “best effort”; a hard boundary is missing.

**Minimal Reproducible Examples**

**Repro 1: Closure returns reference to owned capture; use after closure scope (should be rejected).**
```lisp
(def use_shared (pi r (Ref Shared Nat) Nat)
  (lam r (Ref Shared Nat) zero))

(def mk_ref_closure (pi n Nat (pi u Nat (Ref Shared Nat)))
  (lam n Nat
    (let x Nat n
      (lam u Nat (& x)))))

(def bad (pi n Nat Nat)
  (lam n Nat
    (let r (Ref Shared Nat)
      (let f (pi u Nat (Ref Shared Nat)) (mk_ref_closure n)
        (f zero))
      (use_shared r))))
```
Expected: reject (returned ref must be tied to `f`’s lifetime). Risk: accepted due to missing self-borrow lifetime in NLL.

**Repro 2: Axiom/classical laundering via redefinition (core AST sketch).**
```rust
let ax_ty = /* classical_choice_type */;
let ax = Definition::axiom_classical("Ax".into(), ax_ty.clone());
env.add_definition(ax).unwrap();
let use_ax = Definition::total("use_ax".into(), ax_ty.clone(), Rc::new(Term::Const("Ax".into(), vec![])));
env.add_definition(use_ax).unwrap();
// Redefine Ax without classical tag
let ax2 = Definition::total("Ax".into(), ax_ty, Rc::new(Term::Lam(...)));
env.add_definition(ax2).unwrap();
// classical_axiom_dependencies now drops Ax even though use_ax was checked against a classical axiom.
```

**Repro 3: `opaque` does not hide Prop in data fields.**
```lisp
(def opaque MyProp (sort 1) (sort 0))
(inductive Boxed (sort 1)
  (ctor mk (pi p MyProp Boxed)))
```
Expected by README: `opaque` should keep `MyProp` folded. Actual: `is_prop_like` uses `Transparency::All` and rejects `Boxed` as Prop-in-data.

**Fix Plan (Prioritized)**
1. What: Forbid redefinition of existing definitions/inductives by default. Where: `kernel/src/checker.rs` (`add_definition`, `add_inductive`). Why: Prevent TCB tampering and axiom laundering. Tests: Add kernel tests that redefining `Comp`, `Nat`, or `classical_choice` is rejected.
2. What: Add explicit “prelude frozen” flag after prelude load; disallow shadowing of prelude names without `--allow-redefine`. Where: `cli/src/driver.rs` and `kernel/src/checker.rs`. Why: Enforce README’s prelude trust boundary. Tests: CLI integration test attempting to redefine `Nat` after prelude.
3. What: Model closure self-borrow in MIR types (add implicit `&self` arg or explicit region parameter tied to self). Where: `mir/src/lower.rs`, `mir/src/types.rs`, `mir/src/analysis/nll.rs`. Why: Prevent returned references from outliving closure borrow. Tests: Add NLL regression for `bad` closure repro.
4. What: Emit loans for `CallOperand::Borrow` when return type contains references tied to self. Where: `mir/src/analysis/nll.rs` (`check` pass). Why: Tie call-site borrow to returned refs. Tests: Borrowck corpus case for closure returning `&self` field.
5. What: Update `call_operand_type` to reflect borrow-of-self when `CallOperand::Borrow`. Where: `mir/src/analysis/nll.rs:1028-1032`. Why: Ensure region constraints relate self-borrow to output. Tests: NLL test that dropping closure while ref live is rejected.
6. What: Add explicit `opaque` semantics rule: either honor `opaque` everywhere or document exceptions for Prop/borrow inference. Where: `kernel/src/checker.rs:is_prop_like`, `mir/src/lower.rs:borrow_shape_unfold`, README. Why: Align user expectations and defeq predictability. Tests: README promise tests for `opaque` in Prop checks.
7. What: Make axiom-tag classification stable by snapshotting tags at definition time (not name lookup at query time). Where: `kernel/src/checker.rs:axiom_dependencies_with_tag`. Why: Prevent tag laundering via redefinition or tag mutation. Tests: Unit test for redefining axiom name still keeps original tag in dependencies.
8. What: Reserve core names `Comp`, `Eq`, `Nat`, `Bool`, `List`, `False` (and any prelude TCB defs). Where: `kernel/src/ast.rs` reserved lists + `add_inductive`/`add_definition` checks. Why: Protect effect boundary and logical base types. Tests: Reject redefining `Comp` after prelude.
9. What: Add MIR lints for closure return refs to owned captures. Where: `mir/src/lints.rs`. Why: Safety backstop even if full NLL fix is delayed. Tests: Lint triggers on closure returning ref to captured ADT.
10. What: Extend borrowck corpus with cases for closure captures and call-returns-ref-of-self. Where: `mir/tests/borrowck_corpus.rs`. Why: Prevent regressions in NLL. Tests: new corpus cases should fail before fix, pass after.
11. What: Add CLI diagnostic when `opaque` is unfolded during Prop/borrow checks (explain exception). Where: `kernel/src/checker.rs`, `mir/src/lower.rs`. Why: Make opaque exceptions visible to users. Tests: verify diagnostics when `opaque` is unfolded for Prop-likeness.
12. What: Document trusted boundary changes (kernel does ownership/effects). Where: `README.md` + `docs/production.md`. Why: Align contract with implementation until refactor lands. Tests: README promises tests updated accordingly.

**Go/No-Go Checklist for Stdlib Expansion**
- [ ] Redefinition of prelude/TCB names is rejected by default.
- [ ] Closure borrow lifetime is modeled; returning refs tied to `self` is enforced.
- [ ] Axiom/classical dependency tracking is stable against redefinition.
- [ ] `opaque` semantics are explicit and consistent (or documented exceptions).
- [ ] Borrowck corpus includes closure-return-ref regressions.
- [ ] CLI diagnostics clearly indicate when macro boundary or `opaque` exceptions are triggered.
- [ ] README trust-boundary statements match actual enforced behavior.

**Suggested GitHub Issues**
- “Reject redefinition of existing defs/inductives by default” — labels: bug/soundness
- “Model closure self-borrow lifetimes in MIR/NLL” — labels: bug/soundness
- “Stabilize axiom tag tracking against name redefinition” — labels: bug/soundness
- “Clarify or enforce `opaque` semantics in Prop/borrow checks” — labels: design/docs
- “Add closure-return-ref borrowck regression tests” — labels: test
- “Reserve core prelude names (Comp/Nat/Bool/Eq) in kernel” — labels: design/soundness
