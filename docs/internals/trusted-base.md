# Trusted Computing Base (TCB)

In LeanRustLisp, the correctness of the entire system relies on a small set of core components known as the Trusted Computing Base (TCB). If the TCB is correct, then all checked programs are type-safe and adhere to the language's logical consistency.

## The Kernel

The primary component of the TCB is the `kernel` crate.

- **Type Checker**: The rules for type checking (Dependent Pi, Inductives, Sorts) are implemented here.
- **Definitional Equality**: The logic for determining if two terms are definitionally equal (beta-reduction, etc.) must be correct.
- **Inductive Validity**: The checks for positivity and universe consistency for new inductive types.

## What is NOT Trusted

- **Frontend**: The parser, macro expander, and elaborator are *not* trusted. If they produce an invalid Core Term, the Kernel will reject it.
- **Type Inference**: Inference heuristics in the elaborator are a convenience; the result is always verified by the Kernel.

## Auditing

Changes to the `kernel` directory should be audited with extreme care.
