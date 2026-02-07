# Getting Started

## Prerequisites

To build LeanRustLisp (LRL), you need the standard Rust toolchain installed:
1. `rustc`
2. `cargo`

If you don't have these, install them via [rustup.rs](https://rustup.rs).

## Building from Source

Clone the repository and build the workspace:

```bash
git clone https://github.com/leanrustlisp/leanrustlisp
cd leanrustlisp
cargo build
```

The compiled binaries will be in `target/debug`.

## Running the REPL

The easiest way to explore LRL is the Read-Eval-Print Loop (REPL).

```bash
cargo run -p cli
```

You should see a prompt:
```
LRL>
```

Try typing a simple expression:
```lisp
LRL> (add 1 2)
3 : Int
// Result evaluation and type
```

## Running a File

To interpret an LRL file directly:

```bash
cargo run -p cli -- path/to/file.lrl
```

For example, try running one of the tests:
```bash
cargo run -p cli -- tests/simple_test.lrl
```

## Compiling to Binary

To compile an LRL program to a standalone executable:

```bash
cargo run -p cli -- compile path/to/file.lrl -o my_program
./my_program
```

## Debugging and inspection

LRL provides several flags to help you understand what the compiler is doing.

### Macro Expansion
To see how your macros expand, use specific flags. Note that you must provide a file argument.

- `--expand-1`: Expands top-level macros one step.
- `--expand-full`: Fully expands all macros.
- `--trace-expand`: Shows the expansion process step-by-step.

```bash
cargo run -p cli -- --expand-1 path/to/file.lrl
```

### Trace Macros
To see macro expansion traces while running or compiling:
```bash
cargo run -p cli -- --trace-macros path/to/file.lrl
```

### Definitional Equality Fuel
If you hit recursion limits during type checking, you can increase the "fuel" for the definitional equality checker:
```bash
cargo run -p cli -- --defeq-fuel 1000000 path/to/file.lrl
```
