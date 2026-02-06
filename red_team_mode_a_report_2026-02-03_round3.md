# Red Team Mode A Report (Semantic / Pre‑Codegen) — 2026-02-03 Round 3

## Executive summary
- **Termination fixes look solid:** bare self‑reference and let‑alias recursion now error (`BareRecursiveReference`) in the kernel termination checker. `TerminationCtx` tracks recursive aliases and `check_recursive_calls_ctx` rejects them. (`kernel/src/checker.rs` L185–206, L935–989, L1622–1678)
- **Primitive hygiene improved:** `Ref/Shared/Mut` are now reserved primitives and validated with signatures alongside `borrow_*`/`index_*`. (`kernel/src/ast.rs` L103–113; `kernel/src/checker.rs` L4045–4054)
- **Marker validation is now in‑kernel:** marker registry initialization validates marker definitions (unsafe axiom + signature) at add‑time. (`kernel/src/checker.rs` L420–468, L3077–3086)
- **Remaining blocker is MIR call semantics for Fn/FnMut:** calls move the function local, effectively treating Fn/FnMut like FnOnce. This violates the spec’s borrow‑based call semantics and causes the compiler to reject programs the kernel accepts. (`docs/spec/function_kinds.md` L14–18; `mir/src/lower.rs` L575–579; `mir/src/lower.rs` L1626–1655)

## Contract violations
1. **Fn/FnMut are moved on call in MIR (violates borrow‑call contract).**
   - Spec: Fn/FnMut call uses shared/mut borrow of environment. (`docs/spec/function_kinds.md` L14–18)
   - Implementation: `call_operand_for_func` uses `local_operand` for Fn/FnMut, which moves when the local is non‑Copy; tests assert Move for Fn/FnMut. (`mir/src/lower.rs` L575–579, L1626–1655)
   - Impact: Fn/FnMut become effectively FnOnce in MIR, rejecting valid programs and breaking semantic contract.

## Soundness / TCB risks
- **Phase mismatch risk (kernel vs MIR):** kernel accepts repeated Fn/FnMut calls (ownership uses observational/mut‑borrow modes), but MIR consumes the function local. This is a correctness gap between kernel semantics and compiler behavior, causing spurious errors or behavior drift across phases.
- **TCB reduced vs previous round:** reserved primitives and marker validation are now in the kernel, which is good; the remaining risk is mostly compiler correctness rather than kernel soundness.

## Semantic gaps (severity)
- **[High] Fn/FnMut call semantics are wrong in MIR.** Fn/FnMut calls move the function local, so you cannot call a closure twice unless it is Copy; this contradicts the language’s semantics and breaks higher‑order programming.
- **[Low] Documentation drift:** `docs/spec/kernel_boundary.md` still mentions only Fn/FnOnce in the kernel boundary (not FnMut), while FnMut is implemented.

## Minimal reproducible examples
1. **FnMut callable twice (should pass, MIR rejects).**
```lisp
(def use_twice (pi x Nat Nat)
  (lam x Nat
    (let r (Ref Mut Nat) (&mut x)
      (let f (lam y Nat (use_mut r))
        (let _ Nat (f 0)
          (f 0))))))
```
Expected: valid; FnMut permits multiple calls. Actual: MIR lowers calls as Move for FnMut, so the second call is a use‑after‑move error.

2. **Fn callable twice (should pass, MIR rejects).**
```lisp
(def use_fn_twice (pi x Nat Nat)
  (lam x Nat
    (let f (lam y Nat y)
      (let _ Nat (f x)
        (f x)))))
```
Expected: valid; Fn uses shared borrow and is callable multiple times. Actual: MIR moves the function local on first call, so the second call fails.

## Fix plan (prioritized)
1. **Define MIR‑level call semantics for Fn/FnMut** (borrow instead of move).
   - **What:** Add a call operand or terminator field that represents borrowing the function local (shared for Fn, mutable for FnMut).
   - **Where:** `mir/src/lower.rs`, `mir/src/pretty.rs`, `mir/src/codegen.rs`.
   - **Why:** Align call semantics with spec.
   - **Tests:** new MIR unit tests for Fn/FnMut call lowering.
2. **Update `call_operand_for_func`** to use borrow‑call representation for Fn/FnMut (not Move).
   - **Where:** `mir/src/lower.rs`.
3. **Teach ownership analysis** to treat borrow‑call operands as non‑consuming.
   - **Where:** `mir/src/analysis/ownership.rs`.
4. **Teach borrow checker** to model FnMut call borrows (mut‑loan on closure environment).
   - **Where:** `mir/src/analysis/borrow.rs` and/or `mir/src/analysis/nll.rs`.
5. **Adjust capture lowering if needed** so Fn/FnMut closures can be reused without copying env values.
   - **Where:** `mir/src/lower.rs` capture plan, closure env layout.
6. **Update MIR call tests** (replace Move expectations with borrow expectations).
   - **Where:** `mir/src/lower.rs` tests (around `test_call_operand_respects_fn_kind`).
7. **Add borrow‑ck corpus tests** for repeated Fn/FnMut calls.
   - **Where:** `mir/tests/borrowck_corpus.rs`.
8. **Add CLI golden tests** showing Fn/FnMut called multiple times works.
   - **Where:** `cli/tests/pipeline_golden.rs` + snapshots.
9. **Update docs** to reflect FnMut support in kernel boundary and MIR call semantics.
   - **Where:** `docs/spec/kernel_boundary.md`, `docs/spec/mir/typing.md`.
10. **Add regression test in kernel** that multiple Fn/FnMut calls type‑check and remain accepted post‑pipeline.
    - **Where:** `kernel/tests/semantic_tests.rs`, `cli/tests/pipeline_golden.rs`.

## Go / No‑Go checklist (stdlib expansion)
- [ ] Fn/FnMut call semantics are borrow‑based in MIR (no Move).
- [ ] Borrow checker models FnMut call borrows on closure environments.
- [ ] CLI pipeline passes repeated Fn/FnMut call tests.
- [ ] Docs updated for FnMut in kernel boundary and MIR semantics.

## Suggested GitHub issues (titles + labels)
- **“MIR lowers Fn/FnMut calls as Move (should borrow)”** — labels: bug, semantics, mir.
- **“Borrow checker lacks FnMut call‑borrow modeling”** — labels: bug, mir, borrowck.
- **“Update kernel boundary docs for FnMut”** — labels: docs.

