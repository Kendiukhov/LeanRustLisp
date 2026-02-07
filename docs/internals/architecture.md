# Architecture Overview

The LeanRustLisp (LRL) compiler is structured as a pipeline of distinct crates, each with a specific responsibility. This separation is crucial for the "trusted kernel" architecture.

## High-Level Pipeline

1. **Source** (`.lrl`) is parsed into a **Syntax Tree** (`frontend`).
2. **Macros** are expanded to produce a fully expanded Syntax Tree (`frontend`).
3. **Desugaring** converts Syntax to **Surface Terms** (`frontend`).
4. **Elaboration** converts Surface Terms to **Core Terms** (`kernel`), handling type inference and implicit arguments.
5. **Kernel** verifies the Core Terms (type checking, definitional equality).
6. **MIR Lowering** converts Core Terms to **Mid-level Intermediate Representation (MIR)** (`mir`).
7. **Borrow Checking** enforces ownership and lifetimes on MIR (`mir`).
8. **Codegen** translates MIR to target code (Rust/Binary) (`codegen`).

## Crate Responsibilities

### `kernel` (The Trusted Base)
- **Role**: The minimal, trusted core that verifies the correctness of the program.
- **Key Modules**:
  - `ast`: Defines the Core Calculus (terms, inductives, universes).
  - `checker`: Implements type checking rules.
  - `nbe`: Normalization by Evaluation (for definitional equality).
  - `ownership`: Core ownership definitions.

### `frontend` (Untrusted)
- **Role**: User-facing features, parsing, and elaborating into the core.
- **Key Modules**:
  - `parser`: S-expression parser.
  - `macro_expander`: Hygienic macro system implementation.
  - `elaborator`: Type inference and bidirectional typing to produce Core Terms.
  - `diagnostics`: Error reporting.

### `mir` (Optimization & Safety)
- **Role**: Intermediate representation for analysis and optimization.
- **Key Features**:
  - Control-flow graph construction.
  - Borrow checker (NLL-style).
  - Optimizations.

### `codegen` (Backend)
- **Role**: Emitting executable code.
- **Targets**:
  - Rust (transpilation).
  - LLVM (future).

### `cli` (Driver)
- **Role**: Command-line interface and REPL.
- **Features**:
  - Orchestrates the pipeline.
  - Manages compiler flags and modes.

## Data Structures

- **Syntax**: `frontend::surface::Syntax` (S-expressions with spans).
- **SurfaceTerm**: `frontend::surface::Term` (Desugared, unresolved names).
- **CoreTerm**: `kernel::ast::Term` (Fully explicit, dependently typed calculus).
- **Env**: `kernel::checker::Env` (Global environment of definitions and inductives).
