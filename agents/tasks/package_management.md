AGENT TASK: Implement LRL Package Management (Option A + controlled slices of B)

Goal: Add a deterministic, lockfile-driven package/workspace system with Cargo-like behavior (Option A), plus explicit aliasing for ambiguous multiple-version imports (a controlled slice of Option B).

Non-goals (for this task)
- No public package registry or publishing.
- No network fetching beyond basic git dependencies unless trivial.
- No runtime multi-loader. All resolution happens at build time.
- No full Nix-style hermetic builds (optional later).

Core user experience (target)
- `lrl new`, `lrl build`, `lrl test`, `lrl run`
- Packages declare dependencies in `lrl.toml`.
- A lockfile `lrl.lock` pins exact versions + sources (+ hashes if feasible).
- By default, a package can just `import foo` and it resolves to the package’s dependency graph.
- If multiple versions of the same package exist in the graph and an import is ambiguous, the compiler/tool errors and requires explicit aliasing: `import foo@1.2.3 as foo1` or equivalent syntax.

Phase ordering for implementation
Implement in three incremental stages:
1) Workspace + path deps (MVP)
2) Lockfile + deterministic resolution (still local/path, optionally git)
3) Ambiguity detection + explicit versioned imports (slice of B)

Deliverables
A) Documentation (must add)
1) docs/reference/modules-packages.md
   - Define: package identity, workspace, dependency graph, lockfile semantics.
   - Define: default import resolution per dependency graph.
   - Define: ambiguity rule and explicit alias syntax.
2) docs/dev/build.md
   - How to build a workspace, how lockfiles work, how to run examples/tests.

B) Package manifest & lockfile formats
1) Define `lrl.toml` schema (minimal but extensible):
   - [package] name, version, edition
   - [dependencies] entries supporting at least:
     - path = "../foo"
     - (optional in this task) git = "...", rev = "..."
     - version = "semver-range" (can be ignored until stage 2 if you only do path deps first)
   - [workspace] members = [...]
2) Define `lrl.lock` schema:
   - list of resolved packages with:
     - name, resolved_version
     - source (path/git)
     - content hash (nice-to-have; can be omitted MVP but add placeholder field)
     - resolved dependency edges

C) Tooling implementation (CLI)
Add or extend a CLI tool (can be `cli` crate or a new `lrl` binary) to support:
1) `lrl build`
   - reads workspace manifest
   - builds packages in topological order
   - caches build artifacts
2) `lrl run <pkg>` or `lrl run -- <file>`
3) `lrl test`
   - runs kernel/frontend/codegen tests plus golden tests
4) (optional MVP) `lrl clean`

D) Compiler integration: module/import resolution
Implement import resolution as a compile-time step (NOT runtime):
1) Add a module loader / resolver that:
   - given a package root, finds its source files
   - resolves `import foo` to the correct package ID in that package’s dependency graph
2) Implement ambiguity detection:
   - if dependency graph includes multiple packages with same logical name `foo` and the current package/module imports `foo` without disambiguation, error with a clear message:
     “Ambiguous import: foo resolves to foo@1.2.3 and foo@2.0.0. Use explicit import alias.”
3) Implement explicit versioned imports (slice of B):
   - design syntax for disambiguation:
     Option 1: `import foo@1.2.3 as foo1`
     Option 2: `import foo#<package_id> as foo1`
   - Decide which is easier given your parser; document it; implement it.
   - Ensure explicit import selects the correct resolved package instance.

E) Determinism & reproducibility requirements
1) Deterministic resolution:
   - same workspace + lockfile => same dependency graph
2) Lockfile enforcement:
   - For “release mode” builds, refuse to build if lockfile missing or out of date (configurable flag ok).
3) No hidden ambient environment dependency:
   - do not use OS-wide search paths for imports (no sys.path-style behavior).

F) Testing (must add)
1) Unit tests for resolver:
   - single dependency import resolves correctly
   - ambiguity triggers error
   - explicit import resolves correctly
2) Integration tests:
   - a workspace with two packages A and B, A depends on B, import works
   - a workspace with A depending on B@v1 and C depending on B@v2 and a D depending on both => D must alias imports
3) Golden tests:
   - add a `tests/packages/` fixture workspace and run `lrl build` on it in CI

Implementation steps (recommended)
Stage 1: MVP (path deps only)
1) Implement manifest parsing for workspace + packages.
2) Implement “package graph” builder (nodes: packages; edges: deps).
3) Implement build ordering and invoking current compiler pipeline per package.
4) Implement import resolution within a package (only path deps; no versions yet).
5) Add docs + tests.

Stage 2: Lockfile
1) Add lockfile generator: `lrl build` writes/updates `lrl.lock`.
2) Add lockfile reader and enforcement: if lockfile present, use it; if not, generate in dev mode.
3) Ensure deterministic ordering of entries in lockfile.

Stage 3: Multiple versions + aliasing (slice of B)
1) Extend dependencies to allow explicit version pin in manifest (even if only for local fixtures).
2) Simulate multiple versions via two different path deps with same name but different version fields.
3) Add ambiguity detection and explicit import syntax.
4) Update docs + tests.

Acceptance criteria (“done means done”)
- Workspace builds deterministically from `lrl.toml`.
- `lrl.lock` exists, is deterministic, and controls resolution when present.
- Imports resolve per dependency graph, not global paths.
- Ambiguous `import foo` errors with a clear message.
- Explicit alias import works and is documented.
- CI tests cover at least one multi-version ambiguity scenario.

Nice-to-have (only if time remains)
- Content hashes for packages (hash of source tree) recorded in lockfile.
- A `lrl vendor` or `lrl fetch` step (for git deps).
- `lrl fmt`/`lrl doc` placeholders for future.

Notes
- Keep the kernel isolated: package management must not contaminate trusted code.
- Treat this as tooling + compiler frontend responsibility.
- If you need a stable internal ID for packages, use (name, version, source, hash) and derive a short package_id string for internal use and error messages.