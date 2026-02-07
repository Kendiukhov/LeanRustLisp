# Repository Guidelines

## Project Structure & Module Organization
- `Cargo.toml` defines a Rust workspace with crates: `kernel/` (type checker + core), `frontend/` (parser/macro expansion/elaboration), `mir/` (mid-level IR + borrow checking), `codegen/` (Rust code generation), `cli/` (compiler/REPL entrypoint).
- `stdlib/` contains the split prelude stack: `prelude_api.lrl`, backend impl shims (`prelude_impl_dynamic.lrl`, `prelude_impl_typed.lrl`), and shared `std/` modules.
- `tests/` holds `.lrl` programs used for integration/regression checks.
- `docs/` contains design notes and test plans; `report*.md` are historical reports.
- Build artifacts live in `target/` and should not be committed.

## Build, Test, and Development Commands
- `cargo build` -- build all workspace crates.
- `cargo test --all` -- run Rust unit/integration tests across crates.
- `cargo test -p frontend` / `cargo test -p cli` -- focus tests for a single crate.
- `cargo test -p mir --lib` / `cargo test -p frontend --lib` / `cargo test -p cli --lib` -- run fast unit-test slices for MIR lowering, elaboration, and CLI compiler logic.
- `cargo run -p cli -- tests/ownership_test.lrl` -- run a program in the interpreter (loads the default dynamic prelude stack: `prelude_api + std/core + std/data + prelude_impl_dynamic`).
- `cargo run -p cli -- compile tests/ownership_test.lrl` -- compile to Rust (optionally `-o/--output <path>`).
- `cargo run -p cli -- compile-mir tests/ownership_test.lrl` -- lower to MIR for inspection.

## Coding Style & Naming Conventions
- Rust: follow `rustfmt` defaults (4-space indent). Keep modules small and focused.
- Naming: `snake_case` for functions/variables/modules, `CamelCase` for types/traits, `SCREAMING_SNAKE_CASE` for consts.
- LRL files: descriptive `snake_case` names (e.g., `ownership_test.lrl`); definitions generally use lower_snake_case.

## Testing Guidelines
- Rust tests live in `*/tests/*.rs` and `src/*` test modules; snapshots use `insta` in `frontend/tests/snapshots` and `cli/tests`.
- To update snapshots, run `INSTA_UPDATE=always cargo test -p frontend` (or `-p cli`).
- `.lrl` programs in `tests/` are run via the CLI; add new cases alongside related files.
- New unit tests for recent Fn/FnOnce + erased-type changes live in `mir/src/lower.rs`, `frontend/src/elaborator.rs`, and `cli/src/compiler.rs`.

## Commit & Pull Request Guidelines
- Commit messages are short, capitalized imperatives (e.g., "Add ...", "Implement ...", "Remove ...").
- PRs should describe scope, list tests run, and call out snapshot/output changes. Link relevant issues or design docs when available.

## Branch Discipline
- Always work on `main` by default.
- Only create, switch to, or operate on a non-`main` branch when the user explicitly requests it.

## Advice
If you were stuck with an error for a long time and finally found a solution, please document it here in concise form.
- Persistent borrow errors in MIR often trace back to erased/Unit locals being marked non-Copy. Ensure `push_local`/`push_temp_local` set `is_copy` based on the lowered `MirType` and then refresh snapshots; otherwise closures may borrow ephemeral erased args and fail later in borrowck.
