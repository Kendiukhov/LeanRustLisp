# Document B — Typed Backend Implementation Roadmap (Updated, Stage 1 Focus)

**Owner:** Codegen Engineer (MIR → Rust)  
**Scope:** pre-codegen semantics are already validated (kernel + MIR typing + NLL). This document is **only** about the **first stage** of typed Rust codegen from MIR.  
**Non-goal:** redesign MIR, borrow checking, or kernel rules. Assume Document A (“MIR contract”) is in force.

---

## 1) Current situation

### Already in place
- **Unified pipeline**: source → parse → macro expand → elaborate → kernel check → MIR lowering → MIR typing → ownership → NLL → codegen.
- **MIR contract exists**: typed locals (`MirType`), places/projections, CFG, and NLL artifacts.
- **Release-bar checks are green**: core semantic boundaries are enforced in the pipeline.

### Still present (temporary)
- A **dynamic backend** (universal runtime `Value`) may exist as a fallback/debug path.
- Typed backend should gradually replace dynamic backend for supported subsets.

---

## 2) Stage 1 goal (first milestone)

### Goal
Generate **meaningful typed Rust** for a strict initial subset:
- **Non-parameterized ADTs** (inductives without type parameters): `Nat`, `Bool`, and user inductives with concrete field types.
- **Straight-line MIR** + **basic control flow**:
  - locals/temps, assignments, moves
  - constructor creation
  - `switch`/`match` on ADTs / Bool
  - calls to known top-level functions (no higher-order closure conversion in Stage 1 unless already trivial)
- **No tag-check panics** in the typed subset. Any panic must be an intentional runtime check (e.g., bounds check) and documented.

### Non-goals (defer)
- Parametric ADTs / generics (`List<A>`, `Option<A>`).
- Full closure conversion and comprehensive `Fn/FnMut/FnOnce` lowering (Stage 2).
- Effectful `Comp` mapping, IO, concurrency.
- Interior mutability runtime checks (RefCell/Mutex): remain gated until implemented.

---

## 3) Stage 1 supported subset (operational)

The typed backend must either:
- Emit typed Rust for programs whose MIR uses only supported constructs, or
- Reject with a clear “unsupported by typed backend” diagnostic (and `--backend auto` may fall back to dynamic).

### Minimum supported MIR
- Locals/temps with concrete `MirType`:
  - `Nat`, `Bool`, `Unit`
  - `Adt(AdtId)` where all fields are Stage‑1 supported
- Rvalues:
  - `Use(Move(..))`
  - `Use(Copy(..))` only when MIR/kernel says Copy
  - `Ctor(AdtId, CtorId, args...)`
- Terminators:
  - `Return`, `Goto`
  - `Switch` on ADT discriminant / Bool
  - `Call` to a known function def (no higher-order calls unless already representable)
- Borrowing:
  - If MIR includes `Ref` operations, choose one:
    - (A) support via safe Rust references where representable, or
    - (B) reject in typed backend Stage 1 and require dynamic backend.
  Document the choice in `docs/spec/codegen/typed-backend.md`.

---

## 4) Stage 1 deliverables

### D1) Backend subset spec (small)
Create/update: `docs/spec/codegen/typed-backend.md` with:
- Stage 1 supported MIR constructs
- fallback/rejection rules
- “no tag-check panics” rule
- allowed runtime checks (bounds checks only, unless more are implemented)

### D2) Typed ADT emission
- For each Stage‑1 `AdtId`, emit a Rust `enum` with variants for constructors.
- Recursively map field types to Rust types.

### D3) Typed function bodies from MIR
- Emit Rust functions for MIR bodies (CFG → Rust blocks).
- Emit `match` for `Switch` on ADTs / Bool.
- Preserve move/copy semantics as validated by MIR ownership + NLL.

### D4) Deterministic structured codegen
- Avoid raw string concatenation for new code.
- Use a structured Rust AST builder (syn/quote or a minimal internal AST) or a deterministic pretty-printer.
- Stable naming based on `DefId/AdtId/CtorId` (no raw strings).

### D5) Backend selection flags (if not already present)
- `--backend dynamic`
- `--backend typed` (hard error if unsupported)
- `--backend auto` (typed where possible, else dynamic with a warning)

---

## 5) Stage 1 acceptance tests

1) **Compile+run parity**
- For each Stage‑1 program: `--backend typed` output equals `--backend dynamic`.

2) **No tag-check panics**
- Emitted Rust for Stage‑1 subset contains no “Expected Func / wrong tag” panics.
- Runtime execution does not panic except for explicitly documented runtime checks (bounds).

3) **User inductive coverage**
- Include at least one user-defined non-param inductive with multiple ctors + fields + match.

4) **Fallback behavior**
- An unsupported program:
  - `--backend typed` produces a clear diagnostic
  - `--backend auto` falls back to dynamic with a reason

---

## 6) Stage 1 “done” definition

Stage 1 is done when:
- Typed backend runs Nat/Bool + one user-defined non-param inductive end-to-end.
- Outputs match dynamic backend for those programs.
- Typed backend output contains no universal `Value` runtime for that subset (or only behind explicit, documented boundary helpers).
- Output is deterministic and tests are green in CI.

---

## 7) Deferred roadmap (pointers only)

- Stage 2: closure conversion + full `Fn/FnMut/FnOnce` lowering + higher-order calls.
- Stage 3: parametric ADTs and generics (delegate monomorphization to rustc).
- Stage 4: proof erasure ensured in codegen output (no proof objects at runtime).
- Stage 5: effects/capabilities mapping to Rust (Comp rows, IO).
- Stage 6: optional LLVM/Cranelift backend consuming the same MIR.
