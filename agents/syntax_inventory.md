AGENT TASK: Syntax Inventory + 0.1 Syntax Contract Draft (Document What Exists, Define What Must Be Frozen)

Goal: Produce a single, accurate “LRL 0.1 Syntax Contract” document that:
1) documents the syntax currently implemented in code (parser + macro expander + declaration parser + elaborator), and
2) proposes a minimal set of *missing but necessary-to-freeze* syntactic forms (and their exact surface spelling) that should be defined in advance to avoid later breaking changes.

You are NOT asked to implement features. You are asked to:
- audit current syntax,
- document it precisely with examples,
- identify gaps,
- propose a small “frozen core syntax” + “experimental sugar” list.

Deliverables
A) A new document: `docs/spec/syntax_contract_0_1.md` with sections below.
B) A short “diff list” of missing syntax forms that should be added (as GitHub issues), with file pointers (parser/macro/desugar/elaborator) where they likely belong.

Audit targets (code locations to inspect)
- Reader/parser: `frontend/src/parser.rs`, `frontend/src/surface.rs`
- Macro expansion: `frontend/src/macro_expander.rs`
- Top-level forms: `frontend/src/declaration_parser.rs`
- Term elaboration/desugaring: `frontend/src/elaborator.rs` (and `frontend/src/desugar.rs` if present)
- CLI/driver expectations (entry points, prelude loading): `cli/src/driver.rs`, `cli/src/compiler.rs`

====================================================================================================
Part 1 — Document the syntax that exists TODAY (must be evidence-based)
====================================================================================================

1) File & lexical layer (reader)
- What counts as a program (sequence of forms)
- Comments syntax
- Literals supported: integers, strings, symbols (exact rules)
- Whitespace rules
- Error span behavior (how spans are assigned)

2) Syntax objects model (macro hygiene infrastructure)
- Syntax node kinds: list/symbol/int/string/etc.
- Scope model: scopes/ScopeId sets on nodes
- How scopes attach to introduced identifiers
- Quasiquote/unquote/unquote-splicing syntax (exact forms)

3) Top-level forms currently supported (exact surface spelling)
For each:
- syntax shape (BNF-like)
- required arguments
- what it expands/elaborates to (high-level)
- example
- error behavior

Minimum list to check and document if implemented:
- `(def name type value)` and any modifiers: `opaque`, `partial`, `unsafe`, `noncomputable`, attributes like `#[once]`
- `(inductive Name Type (ctor ...) ...)`
- `(ctor Name Type)` format
- `(axiom ...)` format and tags/classification (classical/unsafe)
- `(instance ...)` format (Copy gating, unsafe requirement, etc.)
- `(import ...)` if present
- Any “prelude directive” forms if present

4) Term-level special forms currently supported
Document exact syntax and binder shapes:
- `lam` (binder syntax; attribute placement: `(lam #[once] x T body)` etc.)
- `pi` (explicit and implicit binders `{x T}`)
- `let` (typed or untyped; exact syntax)
- `match` / `case` (exact syntax, how patterns look)
- `fix` syntax (and where it is permitted)
- `quote` / `quasiquote` (macro-time vs runtime; current policy)

5) Attribute & annotation grammar
Document:
- Where attributes can appear (before binder, before def, etc.)
- Known attributes: `#[once]`, `#[fn]`, `#[fnonce]`, etc.
- Function kind annotations if exposed at surface
- Any “panic-free profile” markers if visible

6) Mode boundaries that are already enforced by syntax/rules
- `eval`/Dyn boundary (is there surface `eval` form? where is it forbidden?)
- total/partial boundaries (`fix` forbidden in `def`)
- macro boundary deny semantics at prelude compile time

====================================================================================================
Part 2 — Identify missing syntax that MUST be defined early (minimal additions only)
====================================================================================================

You are to propose syntax only if:
- it is needed to prevent breaking changes while writing stdlib, OR
- it is necessary to express existing semantics/policies clearly in source, OR
- it is required by already-adopted design decisions.

Do NOT propose sugar just because it’s nice. Keep core compact.

For each proposed missing syntax form, include:
- Proposed surface spelling (exact)
- What it desugars/elaborates to (high-level)
- Why it must be frozen early
- Whether it is “core frozen” or “experimental sugar”

Proposed “must-freeze early” candidates (evaluate which already exist vs missing):
A) Module/import baseline (even minimal)
- `import` form (and aliasing)
- module/namespace declaration if needed
Why: stdlib expansion requires stable namespacing.

B) Definition modifiers (must match current policy)
- `opaque def` (if not already)
- `partial def` (must be explicit)
- `unsafe def` (explicit unsafe boundary)
- `noncomputable def` (axiom-dependent computation gating)
Why: these are semantic boundaries.

C) Axiom declaration tags (classical/unsafe)
- exact surface syntax to require tags in production mode (if policy says so)
Why: prevents laundering.

D) Basic “method/struct” surface sugar (if you plan Option-1 objects soon)
- Optional: `(struct Name (field T) ...)` sugar
- Methods as namespaced defs (`def Name.method ...`)
This can be marked “experimental sugar” if not implemented.

E) Multi-argument binder sugar (optional but very helpful)
- `(lam (x A) (y B) body)` / `(pi (x A) (y B) C)`
- `(-> A B C)` sugar
Mark as “sugar,” not required, but propose a standard if you expect early stdlib usage.

F) Indexing surface form (if you plan to expose it)
- `(index xs i)` or similar
Mark experimental unless MIR supports it end-to-end.

G) Pattern-macro / syntax-rules (NOT required early)
- Only mention if you think it’s needed soon; otherwise keep out of 0.1 freeze.

====================================================================================================
Part 3 — “LRL 0.1 Syntax Contract” categorization
====================================================================================================

In the document, produce two explicit lists:

1) FROZEN CORE SYNTAX (0.1)
- All forms that must not change without an edition bump
- Include: reader basics, def/inductive/ctor, lam/pi/let/match, defmacro/quasiquote, effect/totality modifiers, axiom/instance forms, attribute placement.

2) EXPERIMENTAL / SUGAR
- Allowed to change without breaking the “core contract”
- Includes: multi-arg sugar, arrow sugar, struct sugar, indexing sugar, notation frontends.

Also include:
- “Edition bump required if changed” rules.

====================================================================================================
Output requirements
====================================================================================================

- Write `docs/spec/syntax_contract_0_1.md` in Markdown.
- Include concrete examples for every form.
- Use a small grammar section (EBNF-like) ONLY for the frozen core forms.
- Add a “Known discrepancies” section pointing to:
  - code location where behavior differs from docs
  - recommended doc change or code change (but do not implement)

- Provide a final “Missing syntax issues” list:
  - 5–15 GitHub-issue-ready items
  - each includes: title, justification, and likely code locations to implement

Acceptance criteria
- Document is accurate relative to code (no invented syntax).
- Proposed new syntax is minimal and justified as “needed to freeze early.”
- Clear separation between “frozen core” and “sugar/experimental.”