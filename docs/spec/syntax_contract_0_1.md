# LRL 0.1 Syntax Contract (Draft)

This document is an evidence-based snapshot of the syntax currently implemented in the parser, macro expander, declaration parser, desugarer, elaborator, and CLI driver as of 2026-02-05. It also proposes a minimal set of missing syntax that should be frozen early to avoid breaking changes.

Code audit targets (primary sources):
- Reader/parser: `frontend/src/parser.rs`, `frontend/src/surface.rs`
- Macro expansion: `frontend/src/macro_expander.rs`
- Top-level forms: `frontend/src/declaration_parser.rs`
- Term desugaring/elaboration: `frontend/src/desugar.rs`, `frontend/src/elaborator.rs`
- CLI/driver: `cli/src/driver.rs`, `cli/src/compiler.rs`

---

**Part 1 — Syntax That Exists Today (Evidence-Based)**

**1) Reader & Lexical Layer**

Program shape:
- A program is a sequence of forms (zero or more). The parser returns `Vec<Syntax>`.

Comments:
- Line comments start with `;` and run to end of line.

Whitespace:
- Any Unicode whitespace (`char::is_whitespace`) separates tokens.

Delimiters:
- Lists use parentheses: `( ... )`.
- Braced lists use braces: `{ ... }`.
- Indexing uses brackets: `expr[expr]` (see below).

Literals:
- Integers: non-negative decimal digits only (`[0-9]+`). No sign prefix. Parsed as `usize`.
- Strings: double-quoted. Supports escapes `\n`, `\r`, `\t`, `\"`, `\\`. Unknown escapes keep the backslash.
- Symbols: any run of non-whitespace characters excluding `(){}[]`.
- Hole: `_` is a dedicated token, not a symbol.

Indexing:
- Postfix index syntax `expr [ index ]` is parsed as `SyntaxKind::Index`.
- Indexing associates left-to-right and can be repeated: `a[b][c]`.

Quote tokens (reader sugar):
- `'x` => `(quote x)`
- `` `x `` => `(quasiquote x)`
- `,x` => `(unquote x)`
- `,@x` => `(unquote-splicing x)`

Spans:
- Each syntax node carries `Span { start, end, line, col }`.
- `start/end` are byte offsets in the input.
- `line` starts at 1; `col` starts at 0 at line start.
- List and braced list spans cover from their opening delimiter to their closing delimiter.

Parse errors:
- `UnexpectedEof`, `UnexpectedChar`, `UnmatchedParen` are emitted by the parser.

---

**2) Syntax Objects & Macro Hygiene Model**

Syntax node kinds (see `SyntaxKind`):
- `List`, `BracedList`, `Index`, `Symbol`, `String`, `Int`, `Hole`.

Hygiene model:
- Each `Syntax` carries a `scopes: Vec<ScopeId>`.
- Macro expansion introduces a fresh scope id for each macro call and attaches it to all nodes originating from the macro body.
- Macro arguments are substituted verbatim and keep their original scopes.
- Spans of macro-introduced nodes are remapped to the call-site span; substituted arguments keep their original spans.

Identifier resolution in desugaring:
- Desugaring normalizes scope sets (sort + dedup) and resolves references by exact scope-set match.
- The most specific (largest) matching scope set wins.

Quote/quasiquote model:
- `quote` prevents macro expansion under it.
- `quasiquote` expands recursively and handles `unquote` and `unquote-splicing` with nesting depth.
- `unquote` expands its inner expression at depth 1.
- `unquote-splicing` is only valid inside list contexts at depth 1; its expansion must yield a list/braced-list which is spliced.

Reserved macro names:
- Macros cannot use these names, and forms with these heads are not macro-expandable (only their arguments are expanded):
`axiom`, `def`, `defmacro`, `eval`, `import`, `import-macros`, `inductive`, `instance`, `opaque`, `partial`, `noncomputable`, `structure`, `transparent`, `unsafe`.

---

**3) Top-Level Forms (Declarations)**

Top-level forms are parsed after macro expansion. Anything not recognized as a declaration is treated as a term expression.

**(def ...) / (partial ...) / (unsafe ...) / (noncomputable ...)**

Syntax:
- `(def name type value)`
- `(def opaque name type value)`
- `(def transparent name type value)`
- `(partial name type value)`
- `(partial opaque name type value)`
- `(partial transparent name type value)`
- `(unsafe name type value)`
- `(unsafe opaque name type value)`
- `(unsafe transparent name type value)`
- `(noncomputable name type value)`
- `(noncomputable opaque name type value)`
- `(noncomputable transparent name type value)`

Notes:
- `def` and `partial` default to `transparent` if no transparency modifier is given.
- `unsafe` is a totality marker (`Totality::Unsafe`).
- `noncomputable` sets a flag but does not change totality.
- `fix` is rejected in any definition whose totality is not `partial`.

Example:
```lrl
(def id (pi (x (sort 0)) (sort 0)) (lam x (sort 0) x))
(partial diverge (pi (x (sort 0)) (sort 0)) (fix f (pi (x (sort 0)) (sort 0)) (lam x (sort 0) (f x))))
(unsafe opaque raw_ffi (pi (x (sort 0)) (sort 0)) (lam x (sort 0) x))
```

Errors:
- Wrong arity.
- Name must be a symbol.
- Non-`partial` definitions cannot contain `fix`.

**(opaque ...) / (transparent ...)**

Syntax:
- `(opaque name type value)`
- `(transparent name type value)`

These are equivalent to `def` with a fixed transparency.

**(axiom ...)**

Syntax:
- `(axiom name type)`
- `(axiom tag name type)`
- `(axiom (tag1 tag2 ...) name type)`

Tags:
- `classical`, `unsafe` only.

Example:
```lrl
(axiom classical choice (pi (A (sort 0)) (sort 0)))
(axiom (classical unsafe) excluded_middle (sort 0))
```

Errors:
- Name must be a symbol.
- Tags must be symbols or a list of symbols.
- Unknown tags are rejected.
- If CLI flag `--require-axiom-tags` is enabled, empty tags are rejected.

**(inductive ...)**

Syntax:
- `(inductive Name Type ctor ...)`
- `(inductive (attr1 attr2 ...) Name Type ctor ...)`
- `(inductive {attr1 attr2 ...} Name Type ctor ...)`
- `(inductive copy Name Type ctor ...)`
- `(inductive copy (attr1 attr2 ...) Name Type ctor ...)`

Constructor specs:
- `(Name Type)`
- `(Name : Type)`
- `(ctor Name Type)` (keyworded form)

Attributes:
- `copy` is a special attribute that sets `is_copy`.
- Other attributes are treated as inductive type markers (see Attributes section).

Example:
```lrl
(inductive Nat (sort 0)
  (Zero Nat)
  (Succ (pi (n Nat) Nat)))

(inductive copy (indexable) VecDyn (sort 0)
  (Nil (ind VecDyn))
  (Cons (pi (n Nat) (pi (xs (ind VecDyn)) (ind VecDyn)))))
```

Errors:
- Name must be a symbol.
- Attributes must be symbols.
- Each ctor must be a list of the accepted shapes.

**(instance ...)**

Syntax:
- `(instance TraitName Head Requirement*)`
- `(unsafe instance TraitName Head Requirement*)`

Example:
```lrl
(instance Copy (ind Nat))
(unsafe instance Copy (ind Dyn) dyn_copy)
```

Errors:
- Trait name must be a symbol.
- Requires at least `TraitName` and `Head`.

**(defmacro ...)**

Syntax:
- `(defmacro name (arg1 arg2 ...) body)`

Example:
```lrl
(defmacro unless (cond body)
  (quasiquote (if (unquote cond) (quote ()) (unquote body))))
```

Errors:
- Name must be a symbol and not reserved.
- Args must be symbols.
- Arity must be exactly 3 items after the head.

**(module ...)**

Syntax:
- `(module std.list)`

Rules:
- At most one module declaration is allowed per file.
- Module declarations must appear before other declarations in a file.
- Unqualified declaration names are recorded under the module path.

**(import ...)**

Syntax:
- `(import std.list as List)` (recommended)
- `(import std.list)` (default alias is the last module segment, e.g. `list`)
- `(import classical)` (special axiom import form)

Rules:
- Importing modules does not open them into unqualified scope.
- Qualified lookup can use alias prefixes (`List.map`) or full module paths (`std.list.map`).
- Importing an unknown module is an error.

Errors:
- Invalid shape is rejected; only `(import <module>)`, `(import <module> as <alias>)`, or `(import classical)` are accepted.

**(open ...)**

Syntax:
- `(open List)` (open alias)
- `(open std.list)` (open explicit module path)
- `(open list)` is only legal if it resolves uniquely among imported modules/aliases.

Rules:
- Opened modules contribute to unqualified resolution in declaration order.
- If multiple opened modules provide the same unqualified name, unqualified use is an error (no “last open wins”).

Name resolution contract:
- Unqualified lookup order: local binders > current module > opened modules (ordered) > prelude/global unqualified names.
- Imported aliases are qualified-only and do not participate in unqualified lookup unless opened.
- Qualified lookup (`A.x` or `std.list.x`) resolves only through alias/module paths and never falls back to unqualified lookup.
- Qualified names do not resolve to local binders.

**(import-macros ...)**

Syntax:
- `(import-macros "path" "path2" ...)`

Notes:
- This is handled by the CLI driver before macro expansion.
- Each argument must be a string literal.
- Paths are resolved relative to the current file.
- Imports are recursive and cycle-checked.

**Top-level expression**

Any other form or atom is treated as an expression, elaborated, and (in the CLI) evaluated/displayed.

---

**4) Term-Level Special Forms**

**(lam ...)**

Syntax:
- `(lam binder type body)`
- `(lam kind binder type body)`

`kind` tokens:
- `fn`, `fnmut`, `fnonce`
- `#[fn]`, `#[mut]`, `#[once]`

Binder forms:
- `x` (explicit)
- `{x}` (implicit)
- `_` (wildcard binder)

Example:
```lrl
(lam x (sort 0) x)
(lam #[once] {f} (pi (x (sort 0)) (sort 0)) (f x))
```

Errors:
- Arity must be 4 or 5.
- Binder must be a symbol, `{symbol}`, or `_`.

**(pi ...)**

Syntax (without kind token):
- `(pi x T body)`
- `(pi {x} T body)`
- `(pi (x T) body)`
- `(pi {x T} body)`

Syntax (with kind token):
- `(pi fn x T body)`
- `(pi fn (x T) body)`
- `(pi #[fn] x T body)`
- `(pi #[mut] (x T) body)`

Example:
```lrl
(pi (x (sort 0)) (sort 0))
(pi #[mut] {f} (pi (x (sort 0)) (sort 0)) (sort 0))
```

Errors:
- Binder must be `symbol`, `{symbol}`, `(symbol type)`, or `{symbol type}`.
- Arity must match one of the accepted shapes.

**(let ...)**

Syntax:
- `(let name type value body)`

Example:
```lrl
(let x (sort 0) (sort 0) x)
```

Errors:
- Arity must be 4.
- Name must be a symbol.

**(match ...)**

Syntax:
- `(match scrutinee ret_type case+ )`
- `case` form: `(case (Ctor arg1 arg2 ...) body)`

Example:
```lrl
(match xs (sort 0)
  (case (Nil) (sort 0))
  (case (Cons x xs) x))
```

Errors:
- At least one case required.
- Each case must be `(case (Ctor ...) body)`.
- Constructor name must be a symbol.

**(match_list ...)**

Syntax:
- `(match_list scrut param_t ret_t case_nil case_cons)`
- `case_nil` must be `(case (nil t) body)`.
- `case_cons` must be `(case (cons t h tl) body)` (exactly 4 items in pattern).

Notes:
- This form is implemented in the desugarer but appears unused.

**(fix ...)**

Syntax:
- `(fix name type body)`

Notes:
- `fix` is only permitted inside `partial` definitions.

**(eval ...)**

Syntax:
- `(eval code cap)`

Notes:
- Elaboration rejects `eval` when used in a type context.

**(quote ...)**

Syntax:
- `(quote datum)`
- `'datum` reader sugar

Desugaring behavior:
- Lists become `List` constructor chains.
- Integers become `Nat` constructor chains.
- Strings and symbols become lists of character codes (`Nat`) via `quote_syntax`.
- Other syntax nodes become `_`.

String literals in term position:
- `"abc"` desugars to a `List Nat` of character codes (same as `quote` on strings).

**(sort ...)**

Syntax:
- `(sort n)`

Notes:
- `n` is an integer literal.
- Current implementation maps `n` to `Level::Succ^n(Zero)`.

**(ind ...) / (ctor ...) / (rec ...)**

Syntax:
- `(ind Name)`
- `(ctor Name idx)`
- `(rec Name)`

Notes:
- `(rec Name)` is a placeholder; elaboration errors if used without a motive.

**Application and implicit arguments**

Syntax:
- General application is any list not starting with a special-form keyword.
- Each braced singleton argument `{arg}` is treated as an implicit argument.

Example:
```lrl
(f x {y} z)
```

**(app ...)**

Syntax:
- `(app f arg)`
- `(app f {arg})`

Notes:
- Equivalent to a single-step application with explicit/implicit determined by braces.

**(& ...) / (&mut ...)**

Syntax:
- `(& x)` desugars to `(borrow_shared x)`.
- `(&mut x)` desugars to `(borrow_mut x)`.

**Indexing**

Syntax:
- `expr[index]`

Notes:
- Desugars to `SurfaceTermKind::Index`.
- Elaboration rewrites indexing into calls to:
  - `index_vec_dyn` for `VecDyn`
  - `index_slice` for `Slice`
  - `index_array` for `Array`
- Indexing other types is rejected.

---

**5) Attribute & Annotation Grammar**

Function kind annotations:
- `fn`, `fnmut`, `fnonce`
- `#[fn]`, `#[mut]`, `#[once]`
- Accepted only as the optional first argument to `lam` and `pi`.

Lifetime labels (for `Ref` applications):
- `#[label]` is parsed as an index of symbol `#`.
- Used as the first argument to `Ref` to attach a labeled lifetime.

Example:
```lrl
(Ref #[a] T x)
```

Inductive type markers (attributes):
- Recognized markers: `interior_mutable`, `may_panic_on_borrow_violation`, `concurrency_primitive`, `atomic_primitive`, `indexable`.
- `interior_mutable` is only valid together with one of `may_panic_on_borrow_violation`, `concurrency_primitive`, `atomic_primitive`.
- The marker names are validated against environment definitions.

No other general attribute syntax is currently supported.

---

**6) Mode Boundaries Enforced by Syntax/Rules**

- `fix` is rejected in any definition whose totality is not `partial` (`frontend/src/declaration_parser.rs`).
- `eval` is rejected in type context (`frontend/src/elaborator.rs`).
- Macro boundary policy (default: deny) prevents macros from expanding into:
  - `unsafe` forms with arity ≥ 3
  - `eval`
  - `axiom` (tagged or untagged)
  - `(import classical)`
- Prelude macro boundary allowlist is currently empty (`cli/src/lib.rs`).

---

**7) CLI/Driver Expectations**

Prelude loading:
- `compile_file` uses `stdlib/prelude.lrl` if it exists.
- Prelude macros are set as default imports in the macro expander.
- Redefinition of prelude names is blocked when prelude is frozen (default behavior).

Macro imports:
- `(import-macros ...)` is handled before expansion.
- Imported files are parsed, macro-imported recursively, and their `defmacro` forms are registered.
- Cycle detection is enforced.

Axiom tagging policy:
- `--require-axiom-tags` enforces at least one tag on `(axiom ...)`.

---

**Part 2 — Missing Syntax That Should Be Defined Early (Minimal Additions Only)**

Items below remain intentionally minimal after freezing module/import/open behavior.

1) Multi-binder sugar for `lam`/`pi`
- Proposed spelling: `(lam (x A) (y B) body)` and `(pi (x A) (y B) C)`
- Desugars to: nested `lam`/`pi`.
- Why freeze early: common in stdlib; avoids later syntax changes.
- Status: experimental sugar.

2) Arrow sugar for `pi`
- Proposed spelling: `(-> A B C)`
- Desugars to: `(pi _ A (pi _ B C))`.
- Why freeze early: pervasive in type signatures.
- Status: experimental sugar.

3) Term-level string literal semantics
- Proposed spelling: existing string literal `"..."` in term position
- Desugars to: `List Nat` character-code lists (bootstrap choice for 0.1).
- Why freeze early: strings already parse; without a contract, future changes are breaking.
- Status: core frozen.

4) Struct/record surface sugar
- Proposed spelling: `(struct Name (field T) ...)`
- Desugars to: `inductive` + projections + constructor.
- Why freeze early: likely stdlib data modeling; can be optional.
- Status: experimental sugar.

---

**Part 3 — LRL 0.1 Syntax Contract**

**FROZEN CORE SYNTAX (0.1)**
- Reader tokens and delimiters: lists `(...)`, braced lists `{...}`, indexing `expr[expr]`, quote tokens `'`, `` ` ``, `,`, `,@`.
- Literals: non-negative integers, strings, symbols, hole `_`.
- Macro system: `defmacro`, `quote`, `quasiquote`, `unquote`, `unquote-splicing`, reserved macro heads.
- Top-level declarations: `module`, `import` (module + alias + `classical`), `open`, `def`, `partial`, `unsafe`, `noncomputable`, `opaque`, `transparent`, `axiom`, `inductive`, `instance`.
- Macro import directive: `import-macros`.
- Term forms: `lam`, `pi`, `let`, `match`, `fix`, `eval`, `quote`, `sort`, `ind`, `ctor`, `rec`.
- Application and implicit arguments via braced singletons.
- Function kind annotations: `fn`, `fnmut`, `fnonce`, `#[fn]`, `#[mut]`, `#[once]`.
- Lifetime label syntax for `Ref`: `#[label]` as first argument.

**Core Grammar (EBNF-ish)**

```
program      ::= { form }
form         ::= decl | term | macro_import

macro_import ::= "(" "import-macros" string { string } ")"

decl         ::= def | partial | unsafe_def | noncomputable
              | opaque | transparent | axiom | inductive | instance
              | module_decl | import_decl | open_decl | import_classical | defmacro

def          ::= "(" "def" [transparency] name term term ")"
partial      ::= "(" "partial" [transparency] name term term ")"
unsafe_def   ::= "(" "unsafe" name term term ")"
              | "(" "unsafe" "instance" name term { term } ")"
noncomputable::= "(" "noncomputable" [transparency] name term term ")"
opaque       ::= "(" "opaque" name term term ")"
transparent  ::= "(" "transparent" name term term ")"
transparency ::= "opaque" | "transparent"

axiom        ::= "(" "axiom" [axiom_tags] name term ")"
axiom_tags   ::= symbol | "(" { symbol } ")"

inductive    ::= "(" "inductive" [ind_attrs] name term { ctor_spec } ")"
ind_attrs    ::= "copy" [attr_list] | attr_list
attr_list    ::= "(" { symbol } ")" | "{" { symbol } "}"
ctor_spec    ::= "(" symbol term ")" | "(" symbol ":" term ")" | "(" symbol symbol term ")"

instance     ::= "(" "instance" name term { term } ")"
module_decl  ::= "(" "module" symbol ")"
import_decl  ::= "(" "import" symbol ")"
              | "(" "import" symbol "as" symbol ")"
open_decl    ::= "(" "open" symbol ")"
import_classical ::= "(" "import" "classical" ")"

defmacro     ::= "(" "defmacro" name "(" { symbol } ")" syntax ")"

term         ::= atom | list_term
atom         ::= symbol | int | hole
list_term    ::= "(" term_head { term | implicit_arg } ")"
implicit_arg ::= "{" term "}"

term_head    ::= "lam" | "pi" | "let" | "match" | "fix" | "eval" | "quote" | "sort"
              | "ind" | "ctor" | "rec" | term

lam          ::= "(" "lam" [fn_kind] binder term term ")"
pi           ::= "(" "pi" [fn_kind] (binder term term | binder_pair term) ")"
fn_kind      ::= "fn" | "fnmut" | "fnonce" | "#[fn]" | "#[mut]" | "#[once]"

binder       ::= symbol | hole | "{" symbol "}"
binder_pair  ::= "(" symbol term ")" | "{" symbol term "}"
```

**EXPERIMENTAL / SUGAR (May Change Without Edition Bump)**
- `match_list` special form.
- `app` single-step application form.
- `&` and `&mut` borrow sugar.
- Indexing semantics beyond the current VecDyn/Slice/Array rewrite.
- Future binder-group sugar and arrow sugar (proposed above).
- Future struct/record sugar (proposed above).

**Edition Bump Required If Changed**
- Any change to the tokenization of symbols, integers, strings, or `_`.
- Any change to list/braced/index/quote tokenization or precedence.
- Any change to the surface spelling or arity of core declarations and term forms.
- Any change to macro hygiene scope attachment or `quote`/`quasiquote` behavior.

---

**Known Discrepancies (Code vs. Expected Contract)**

None known after the 2026-02-05 discrepancy fixes.

---

**Missing Syntax Issues (GitHub-Issue-Ready, 5–15 items)**

1) Implement multi-binder sugar for `lam`/`pi`
Justification: keeps stdlib readable and avoids later syntactic churn.
Likely code locations: `frontend/src/desugar.rs`, `frontend/src/parser.rs` (if needed).

2) Implement arrow sugar `(-> A B ...)`
Justification: standard in type signatures; freezes surface syntax early.
Likely code locations: `frontend/src/desugar.rs`, `frontend/src/parser.rs` (if needed).

3) Add struct/record surface sugar
Justification: common data modeling; better to stabilize early if planned.
Likely code locations: `frontend/src/declaration_parser.rs`, `frontend/src/desugar.rs`, `kernel` inductive generation.

4) Move `match_list` into prelude sugar/macros and remove core special-case parser/desugar support
Justification: currently hardcoded and unused; should be either promoted to core or moved to prelude macros.
Likely code locations: `frontend/src/desugar.rs`, `stdlib/prelude.lrl`.

5) Add explicit syntax for grouped def modifiers
Justification: current mix of `(def opaque ...)` and `(opaque ...)` is easy to misuse.
Likely code locations: `frontend/src/declaration_parser.rs`.

6) Add module export controls (future)
Justification: current module model exports all names by prefix; explicit export lists may be needed as stdlib scales.
Likely code locations: `frontend/src/declaration_parser.rs`, `cli/src/driver.rs`, `kernel` env policy hooks.
