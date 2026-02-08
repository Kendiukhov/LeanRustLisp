# LeanRustLisp (LRL) 0.1 Alpha

LeanRustLisp (LRL) is an experimental language that combines:

- dependent types and proof-aware checking
- ownership and borrow checking
- hygienic Lisp-style macros

LRL is currently in **alpha**. The compiler pipeline is usable, but the language surface, prelude, and backend coverage are still evolving.

## Current State (Codebase-Backed)

Implemented in the current tree:

- Workspace crates: `kernel`, `frontend`, `mir`, `codegen`, `cli`
- End-to-end pipeline: parse -> macro expansion -> elaboration -> kernel checks -> MIR lowering -> MIR typing/ownership/NLL checks -> Rust codegen
- CLI modes:
  - interpret a file
  - interactive REPL
  - compile to native binary (`typed`, `dynamic`, `auto` backend modes)
- Macro tooling (`--expand-1`, `--expand-full`, `--trace-expand`, `--trace-macros`)
- Axiom tracking and opt-in execution for axiom-dependent definitions
- Definitional equality fuel control (`--defeq-fuel`, `LRL_DEFEQ_FUEL`)

Alpha constraints you should expect:

- Syntax is not fully frozen yet; follow the syntax contract doc linked below.
- `compile` and `compile-mir` default to `--backend auto` (typed-first, fallback to dynamic with warning when needed).
- `compile-mir` is a legacy name; it still runs the full compile pipeline and emits a binary.
- Prelude loading uses a shared API + backend platform layers:
  - `stdlib/prelude_api.lrl` + `stdlib/prelude_impl_dynamic.lrl` (dynamic / interpreter / REPL)
  - `stdlib/prelude_api.lrl` + `stdlib/prelude_impl_typed.lrl` (typed / auto compile)
- You may see startup warnings from prelude axiom/primitive declarations in alpha workflows.

## Stdlib Status (Alpha)

- Milestone-1 core surface is present in shared stdlib modules:
  - core: Nat/Bool helpers
  - data: List/Option/Result/Pair basics
  - control: minimal `Comp` helpers (`comp_pure`, `comp_bind`)
- Prelude loading now includes shared core/data stdlib modules plus backend platform layer:
  - typed/auto: `prelude_api + std/core(nat,bool) + std/data(list,option,result,pair) + prelude_impl_typed`
  - dynamic: `prelude_api + std/core(nat,bool) + std/data(list,option,result,pair) + prelude_impl_dynamic`
- `std/control/comp.lrl` exists as an alpha helper module but is not in the default prelude stack yet.
- Current backend caveat:
  - typed backend is the primary target for Option/Result/Pair alpha smoke workflows
  - Option/Result helper behavior is currently guaranteed only for the smoke-tested positive paths
  - dynamic overlap remains conservative (Nat/Bool/List-first)

## Quick Start

### Prerequisites

- For prebuilt CLI binaries: no repo build step is required.
- For `compile` / `compile-mir`: Rust (`rustc`) is still required.
- For building from source: Rust toolchain (`cargo`, `rustc`).

### Use prebuilt binary package (no `cargo build`)

This repository now includes a host-target package under:

- `dist/aarch64-apple-darwin/`

The package layout is:

- `cli` (prebuilt executable)
- `stdlib/` (runtime prelude + stdlib files)

Run from inside the package directory so relative `stdlib/...` paths resolve:

```bash
cd dist/aarch64-apple-darwin
./cli --help
./cli run /absolute/path/to/program.lrl --backend typed
```

If you use `compile` or `compile-mir` from that binary, `rustc` must be installed because those commands invoke Rust compilation.

### Build

```bash
cargo build
```

### Run a program (`run` command)

```bash
cargo run -p cli -- run tests/simple_test.lrl
```

For visible `print` side effects, use typed backend:

```bash
cargo run -p cli -- run tests/hello.lrl --backend typed
```

Notes:

- `run` defaults to `--backend dynamic`.
- `--backend typed` for `run` is currently supported for direct `.lrl` file targets.
- Program entry is a top-level definition (the last deployed `def`), for example:

```lisp
(def main Text
  (print "Hello, world!"))
```

A bare top-level expression like `(print "Hello, world!")` is not used as executable entry.

### Run a program (interpreter shortcut)

```bash
cargo run -p cli -- tests/simple_test.lrl
```

### Start REPL

```bash
cargo run -p cli --
```

Inside REPL, run `:help` to list commands (`:load`, `:type`, `:eval`, `:expand-*`, `:panic-free`, `:axioms`, ...).

### Compile to binary

```bash
cargo run -p cli -- compile tests/simple_test.lrl -o build/simple_test_bin
./build/simple_test_bin
```

### Backend selection

```bash
# Default (typed-first, dynamic fallback)
cargo run -p cli -- compile tests/simple_test.lrl --backend auto -o build/out_auto

# Force typed backend
cargo run -p cli -- compile tests/simple_test.lrl --backend typed -o build/out_typed

# Force dynamic backend
cargo run -p cli -- compile tests/simple_test.lrl --backend dynamic -o build/out_dynamic
```

Use `--backend auto` for normal alpha usage. The `dynamic` path remains a fallback/debug backend and can still differ from typed behavior outside the documented overlap subset.

### Compile via `compile-mir` command

```bash
cargo run -p cli -- compile-mir tests/simple_test.lrl
./output
```

`compile-mir` currently compiles and emits `./output` by default (unless you use other compile entry points with `-o`).

## CLI Flags You Will Use Often

- `--expand-1`, `--expand-full`, `--trace-expand`: inspect macro expansion for a file
- `--trace-macros`: print macro expansion trace during normal processing
- `--panic-free`: reject panic-requiring paths (including interior mutability/runtime borrow checks)
- `--macro-boundary-warn`: downgrade macro-boundary violations to warnings (user code)
- `--require-axiom-tags`: require axiom tags (`classical`/`unsafe`)
- `--allow-axioms`: allow running/compiling axiom-dependent definitions
- `--allow-redefine`: disable prelude freeze guard (unsafe)
- `--defeq-fuel N`: override definitional equality fuel for this run

Example:

```bash
LRL_DEFEQ_FUEL=200000 cargo run -p cli -- tests/simple_test.lrl
cargo run -p cli -- --defeq-fuel 200000 tests/simple_test.lrl
```

## Suggested Alpha Test Commands

```bash
cargo test --all
cargo test -p cli --test pipeline_golden
cargo test -p cli --test pipeline_negative
cargo test -p cli --test typed_backend
cargo test -p cli --test backend_conformance -- --test-threads=1
```

Snapshot-based suites:

```bash
INSTA_UPDATE=always cargo test -p frontend
INSTA_UPDATE=always cargo test -p cli
```

## Project Map

- `kernel/`: core calculus, type checker, definitional equality, kernel invariants
- `frontend/`: parser, macro expander, desugar/elaborator, diagnostics
- `mir/`: MIR, typing/ownership/NLL checks, transforms, codegen layers
- `codegen/`: backend support crate
- `cli/`: REPL, compile driver, command-line entrypoint
- `stdlib/`: prelude API/platform files (`prelude_api.lrl`, `prelude_impl_dynamic.lrl`, `prelude_impl_typed.lrl`)
- `tests/`: `.lrl` programs for integration/regression
- `cli/tests/`: pipeline, backend, diagnostics, and conformance tests

## Documentation Links

Language and pipeline:

- Syntax contract (draft): `docs/spec/syntax_contract_0_1.md`
- Kernel boundary / trust model: `docs/spec/kernel_boundary.md`
- Core calculus: `docs/spec/core_calculus.md`
- Ownership model: `docs/spec/ownership_model.md`
- Function kinds (`Fn` / `FnMut` / `FnOnce`): `docs/spec/function_kinds.md`
- Macro system: `docs/spec/macro_system.md`
- Phase boundaries: `docs/spec/phase_boundaries.md`
- Mode boundaries (Total/Partial/Unsafe): `docs/spec/mode_boundaries.md`

MIR and backend:

- MIR overview: `docs/spec/mir/mir.md`
- MIR borrows/regions: `docs/spec/mir/borrows-regions.md`
- MIR NLL constraints: `docs/spec/mir/nll-constraints.md`
- MIR typing: `docs/spec/mir/typing.md`
- Typed backend spec: `docs/spec/codegen/typed-backend.md`
- Prelude API contract: `docs/spec/prelude_api.md`
- Architecture notes: `docs/dev/architecture.md`

Diagnostics and examples:

- Diagnostic codes: `docs/diagnostic_codes.md`
- Example programs: `code_examples/`
- CLI integration programs: `tests/`

## License

Dual licensed under **Apache-2.0 OR MIT** (`LICENSE`).
