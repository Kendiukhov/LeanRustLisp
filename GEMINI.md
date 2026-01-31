# Gemini Code Assistant Context: LeanRustLisp (LRL)

This document provides context for the Gemini code assistant about the LeanRustLisp (LRL) project.

## 1. Project Overview

LeanRustLisp (LRL) is an experimental programming language and compiler written in Rust. Its primary goal is to synthesize features from three distinct language families:

*   **Lean-grade specification**: Dependent types, inductive types, and theorem proving capabilities, with a small trusted kernel for soundness.
*   **Rust-grade resource discipline**: Systems-level performance with explicit ownership, borrowing, and lifetime semantics to ensure memory and data-race safety.
*   **Lisp-grade extensibility**: S-expression based syntax (`.lrl` files) that is programmable via a hygienic macro system.

The project is architected as a Rust workspace with several distinct crates that work in concert:

*   `kernel`: The trusted core of the language. It defines the core Abstract Syntax Tree (AST), and implements the fundamental logic for type checking (based on a Calculus of Inductive Constructions), evaluation, and definitional equality.
*   `frontend`: The public-facing part of the compiler. It is responsible for parsing the s-expression syntax of `.lrl` files, expanding macros, and "elaborating" the surface syntax into the more explicit core AST that the kernel can verify.
*   `cli`: A command-line interface to interact with the LRL compiler. It provides a REPL (Read-Eval-Print Loop) and subcommands for compiling files.
*   `codegen`: Responsible for the final stage of compilation, translating LRL's internal representation into another language (currently Rust).
*   `mechanization`: Contains a formalization of the language's core calculus using the Lean proof assistant, aiming to mathematically prove its soundness (e.g., type safety via progress and preservation theorems).

## 2. Building and Running

The project uses the standard Rust toolchain (Cargo).

### Building

To build all packages in the workspace:
```bash
cargo build
```

### Testing

The project has a strong emphasis on testing. To run the full test suite for all crates:
```bash
cargo test
```

### Running the CLI

The `cli` crate is the main entry point for developers using the language.

**Start the REPL:**
```bash
cargo run -p cli
```

**Execute an LRL file:**
```bash
cargo run -p cli -- tests/compile_test.lrl
```

**Compile an LRL file to Rust:**
```bash
cargo run -p cli -- compile tests/compile_test.lrl
```
This will generate a `output.rs` file in the `build/` directory.

## 3. Development Conventions

*   **Language:** The project is written in idiomatic Rust (2021 edition).
*   **Architecture:** The separation between the `frontend` (untrusted, complex), `kernel` (trusted, minimal), and `codegen` is a core design principle. Changes should respect these boundaries.
*   **Testing:** New features or bug fixes should be accompanied by tests. The `kernel` crate contains many examples of how to write tests for the core logic.
*   **Formalism:** The theoretical underpinnings are specified in the `docs/spec/` directory and mechanized in the `mechanization/` directory. The implementation should follow this specification.
*   **Phased Development:** The project follows a detailed, phased development plan, starting with formal specification, then kernel implementation, and building out features from there.
*   **Syntax:** The surface language uses s-expressions. An example can be found in `tests/compile_test.lrl`.

```lisp
;; tests/compile_test.lrl

(def x Nat (succ (succ zero)))
(def result Nat (add x x))
result
```
