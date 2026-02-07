# Community & Trust

## Trusted Computing Base (TCB)

LRL employs a strict separation between **Trusted** and **Untrusted** components to minimize the attack surface for critical bugs.

| Component | Trust Level | Role |
|-----------|-------------|------|
| `kernel` crate | **Trusted** | The only code that must be correct for logical soundness. If the kernel has a bug, proofs may be unsound. |
| `frontend` | Untrusted | Parses and elaborates code. Bugs cause compile errors, not false proofs. |
| `codegen` | Untrusted | Generates Rust/MIR. Bugs may cause runtime crashes, not unsound proofs. |
| `cli` | Untrusted | User interface only. |

---

## Kernel Guarantees (P1–P8)

These are the **release bar promises** that the kernel enforces. Every release is validated against these guarantees.

### P1: Kernel Boundary Enforcement

All definitions and expressions are re-checked by the kernel before acceptance. No production path can bypass kernel validation.

**What this means**: Even if the elaborator or frontend has bugs, the kernel acts as a final gatekeeper. Malformed or unsound terms are rejected.

---

### P2: Totality Boundary

- `def` forbids general recursion (`fix`) and partial constructs (non-terminating code).
- `partial def` is the only place where general recursion is allowed.
- Partial constructs cannot appear in types or definitional equality checks.

**What this means**: Proofs and type-level computations are guaranteed to terminate. Only explicitly marked `partial def` can contain potentially non-terminating code.

---

### P3: Prop/Erasure Safety

- `Prop`-like types are correctly classified (including opaque aliases).
- Large elimination from `Prop` into runtime data is forbidden (unless explicitly allowed).
- Proof erasure cannot be bypassed via aliasing or opaque wrappers.

**What this means**: Proofs are computationally irrelevant at runtime. You cannot accidentally leak proof terms into executable code.

---

### P4: Macro Boundary & Hygiene

- The macro boundary `Deny` works after full expansion (including quasiquote) and cannot be bypassed.
- Hygiene behavior matches the documented policy—macros cannot accidentally capture or shadow user bindings.

**What this means**: Macros are sandboxed. A macro cannot smuggle unsafe constructs past the boundary, and variable capture is controlled.

---

### P5: Borrow/Lifetime Safety (MIR/NLL)

- MIR-level borrow checking rejects aliasing, deref, and projection errors.
- Lifetime labels are not laundered across kernel/MIR boundaries.
- MIR lowering does not erase types in ways that bypass borrow/move/copy enforcement.

**What this means**: Memory safety is enforced at the MIR level, similar to Rust's borrow checker. Use-after-free and data races are caught before code generation.

---

### P6: Axiom/Noncomputable Policy

- Logical axioms (like classical logic) require `noncomputable` or `unsafe` markers.
- Runtime primitives are not misclassified as logical axioms.
- Macro boundaries cannot smuggle axioms into the prelude under `Deny`.

**What this means**: You always know when you're using axioms that might affect logical consistency or computability.

---

### P7: Interior Mutability Policy

- If `RefCell`/`Mutex` runtime checks are not implemented, safe usage must be gated or forbidden.
- If enabled, runtime checks are actually emitted (no silent no-ops in "safe" mode).

**What this means**: Interior mutability follows Rust's model—either the compiler proves safety, or runtime checks enforce it. There are no silent gaps.

---

### P8: Definitional Equality Fuel/Transparency

- Fuel exhaustion is diagnosable and never misreported as success.
- Opaque/transparency behavior matches documented policy.

**What this means**: When the type checker gives up on proving equality (due to computation limits), it tells you clearly instead of silently accepting or rejecting.

---

## Reporting Issues

If you find a soundness bug (e.g., you can prove `False`), please report it immediately!

- **GitHub Issues**: [Open an Issue](https://github.com/Kendiukhov/LeanRustLisp/issues)
- **Security**: See [Security Policy](dev/security.md)

---

## Join Us

- **GitHub Discussions**: Ask questions and share ideas.
- **Contribution**: See our [Contributing Guide](dev/contributing.md).

We welcome all contributors interested in type theory, Rust, and compiler design.
