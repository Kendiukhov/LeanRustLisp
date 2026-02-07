# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

LeanRustLisp (LRL) is an experimental programming language combining:
- **Lean-grade specification**: Dependent types, inductive types, theorem proving with a small trusted kernel
- **Rust-grade resource discipline**: Ownership, borrowing, lifetime semantics
- **Lisp-grade extensibility**: S-expression syntax with hygienic macros

## Build Commands

```bash
cargo build                                    # Build all packages
cargo test                                     # Run all tests
cargo run -p cli                               # Start REPL
cargo run -p cli -- <file.lrl>                 # Execute LRL file
cargo run -p cli -- compile <file.lrl>         # Compile to Rust (outputs to build/output.rs)
```

## Architecture

Four-crate workspace with **trusted kernel design**:

```
User Input (.lrl s-expressions)
    │
    ▼
FRONTEND (frontend/) - UNTRUSTED
├── parser.rs      → Syntax nodes with span/scope tracking
├── macro_expander.rs → Hygienic macro expansion
├── elaborator.rs  → Surface syntax → kernel::Term (de Bruijn indexed)
└── surface.rs     → Surface syntax types
    │
    ▼
KERNEL (kernel/) - TRUSTED CORE
├── ast.rs         → Term, Level, InductiveDecl (CIC-based)
├── checker.rs     → Type checking, inference, reduction (WHNF, beta/iota/eta)
└── ownership.rs   → Affine type checking for resources
    │
    ▼
CODEGEN (codegen/) - Rust emission with type erasure
    │
    ▼
CLI (cli/) - REPL and file compilation
```

**Critical boundary**: The frontend is untrusted and elaborates to the minimal trusted kernel. Changes must respect this separation.

## Key Implementation Details

- **De Bruijn indices**: Variables are `Term::Var(usize)` where 0 is most recently bound
- **Universe hierarchy**: `Sort(Level)` with impredicativity support for Prop
- **Inductive types**: Full CIC-style with automatic recursor generation
- **Definitional equality**: WHNF reduction with beta, iota (pattern matching), eta

## Language Syntax (S-expressions)

```lisp
;; Inductive type definition
(inductive Nat (sort 0)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))

;; Function definition
(def add (pi n Nat (pi m Nat Nat))
  (lam n Nat
    (lam m Nat
      (match n Nat
        (case (zero) m)
        (case (succ m' ih) (succ ih))))))

;; Macro definition
(defmacro id (x) x)
```

## REPL Commands

`:type <expr>`, `:eval <expr>`, `:load <file>`, `:help`, `:quit`

## Safety Fragments

- `def`: Total (must terminate), can appear in types
- `partial def`: General recursion, cannot appear in types
- `unsafe def`: FFI/raw pointers, explicitly marked

## Project Resources

- `stdlib/prelude_api.lrl` + `stdlib/prelude_impl_{dynamic,typed}.lrl` - Split prelude contract and backend shims
- `docs/spec/` - Formal specifications (core_calculus.md, kernel_definition.md, ownership_model.md)
- `mechanization/` - Lean proofs of language soundness
- `tests/` - Integration test files (.lrl)
