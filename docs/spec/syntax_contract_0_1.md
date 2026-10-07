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
- Integers: decimal digits with an optional leading `-` (`-?[0-9]+`), parsed as `i64` (`F0004` invalid literal, `F0005` out of range). A non-negative literal desugars to a `Nat` (`succ`/`zero` chain), a negative one to `int_neg` applied to its magnitude (`Int`).
- Decimals: `-?[0-9]+.[0-9]+` is a float literal (`F0006` if it does not parse as `f32`); it desugars to `float16` applied to the literal's IEEE half-precision bits (`Float`).
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
- Desugaring normalizes scope sets (sort + dedup) and resolves a reference to a local binder whose scope set is a **subset** of the reference's scope set (a reference with scopes never resolves to an unscoped binder).
- The most specific (largest) matching scope set wins.
- This covers local binders only: macro names and global names are resolved by name at the use site (see `docs/spec/macros/hygiene.md`).

Quote/quasiquote model:
- `quote` prevents macro expansion under it.
- `quasiquote` expands recursively and handles `unquote` and `unquote-splicing` with nesting depth.
- `unquote` expands its inner expression at depth 1.
- `unquote-splicing` is only valid inside list contexts at depth 1; its expansion must yield a list/braced-list which is spliced.

Reserved macro names:
- Macros cannot use these names, and forms with these heads are not macro-expandable (only their arguments are expanded):
`axiom`, `def`, `defmacro`, `eval`, `import`, `import-macros`, `inductive`, `instance`, `module`, `open`, `opaque`, `partial`, `noncomputable`, `structure`, `transparent`, `unsafe`.

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
- `(match scrutinee ret_type case+ )` — constant motive: every case, and the whole `match`, has
  type `ret_type`.
- `(match scrutinee (motive M) case+ )` — explicit (dependent) motive. A list whose head is the
  symbol `motive` in the return position is always read as this form.
- `case` form: `(case (Ctor arg1 arg2 ...) body)`

Patterns: the names bind, in order, the constructor's explicit fields (binders after the
inductive's parameters; implicit `{...}` fields are not named), each recursive field being
followed by its induction hypothesis (`(case (succ k ih) ...)`, `(case (vcons h t ih) ...)`).
The parameters are the leading binders that every constructor passes unchanged to the result
type; the kernel infers them from the constructor types, also for binders the arity writes as
indices and the constructor writes explicitly. In
`(inductive T (pi n Nat (sort 1)) (ctor mk (pi n Nat (T n))))`, `n` is a parameter and `mk` has
no field, so its case is `(case (mk) ...)` (the value of `n` is the scrutinee type's argument).
Surplus pattern names are ignored; a case body that uses one is rejected with `F0223`
(`Case mk in match on T binds 1 variable(s), but the constructor provides 0 ...; 'n' is not
bound`).
Every constructor needs exactly one case, impossible ones included. A `match` elaborates to the
inductive's recursor applied to the parameters, the motive, one minor premise per case, the
scrutinee's indices and the scrutinee.

Explicit motive: `M` is a function over the scrutinee type's indices and the scrutinee itself,
returning a sort. For a scrutinee of type `I params i_1 ... i_k`, `M` must have type
`(pi j_1 J_1 ... (pi j_k J_k (pi x (I params j_1 ... j_k) (sort u))))`, e.g.
`(lam k Nat (lam w (Vec A k) T))` for `Vec A n` (one index), or `(lam k Nat T)` for `Nat` (no
index). Each case body is checked against `M` applied to the constructor's indices and to the
constructor applied to the pattern variables; an induction hypothesis for a recursive field `t`
has type `M` applied to `t`'s indices and `t`; the type of the whole `match` is `M` applied to the
scrutinee's indices and the scrutinee. There is no index unification: a case that is impossible
for the scrutinee's indices is still written, against the motive's value at that constructor
(for instance returning a unit value). The kernel re-checks the elaborated recursor application.

Examples:
```lrl
;; constant motive
(match n Nat
  (case (zero) zero)
  (case (succ k ih) (succ ih)))

;; dependent motive: a total head on a non-empty vector
(match v (motive (lam k Nat (lam w (Vec A k)
                   (match k (sort 1) (case (zero) Unit) (case (succ k1 ih) A)))))
  (case (vnil) unit)
  (case (vcons h t ih) h))

;; dependent motive over Nat: a proof by induction of (Eq Nat (add n zero) n), where
;; cong : (f : A -> B) -> Eq A x y -> Eq B (f x) (f y) (x, y implicit) is itself a match on the
;; equality proof with the motive (lam b A (lam w (Eq A x b) (Eq B (f x) (f b))))
(match n (motive (lam k Nat (Eq Nat (add k zero) k)))
  (case (zero) (refl Nat zero))
  (case (succ k ih) (cong succ ih)))
```

Errors:
- At least one case required.
- Each case must be `(case (Ctor ...) body)`.
- Constructor name must be a symbol.
- `(motive ...)` must contain exactly one term.
- Elaboration: unknown, duplicate or missing constructor cases (`F0213`/`F0212`/`F0211`); a motive
  whose type is not of the required shape is a type mismatch (`F0205`).

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
- `"abc"` desugars to a `Text` value: the `text` constructor applied to the character codes as `List Nat` (built in chunks joined with `append`; codes up to 99 use the prelude constants `__nat_ascii_<code>`). `quote` on a string still yields a plain `List Nat` of character codes.

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
- Recognized markers: `interior_mutable`, `may_panic_on_borrow_violation`, `concurrency_primitive`, `atomic_primitive`, `indexable`, `affine`.
- `interior_mutable` is only valid together with one of `may_panic_on_borrow_violation`, `concurrency_primitive`, `atomic_primitive`.
- The marker names are validated against environment definitions, except `affine`, which is built into the kernel.
- `affine` makes the type non-Copy (no derived Copy instance; explicit Copy instances and `copy` + `affine` are rejected with `K0052`); see `docs/spec/ownership_model.md` §1.2.

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
- compile paths load `stdlib/prelude_api.lrl` first, then backend impl:
  - dynamic: `stdlib/prelude_impl_dynamic.lrl`
  - typed/auto: `stdlib/prelude_impl_typed.lrl`
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
- Desugars to: a `Text` value wrapping a `List Nat` of character codes (see "String literals in term position").
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

**Stabilization Gates (Accepted)**

1) Canonical modifier authoring form
- Policy:
Canonical authoring uses `def` forms with modifiers in fixed positions; legacy spellings remain compatibility aliases with warnings.
- Why:
Canonical syntax is required for formatter/linter/style-guide convergence and avoids ecosystem fragmentation.
- Gate to enforce canonical-only:
Stdlib compiles cleanly under canonical form and an auto-formatter (or rewrite tool) is available.

2) Dedicated `String` rollout
- Policy:
Keep string literals as `List Nat` for 0.1; introduce `String` later with migration sugar.
- Why:
Avoids premature runtime representation commitments while typed backend work is still stabilizing.
- Planned migration:
Introduce `String` as either inductive or primitive opaque with explicit operation contracts; update literal desugaring to `String`; keep compatibility mode (`--edition 0.1`) where literals remain `List Nat` as needed.
- Gate to introduce `String`:
Typed backend Stage 1 is stable and runtime representation contract is ready to freeze.

3) Struct/record freeze
- Policy:
Keep struct/record syntax experimental for 0.1.
- Why:
Field semantics and derived-instance behavior are expensive to change once libraries depend on them.
- Gate to freeze:
Desugaring to inductive/projections is agreed and minimal derivation story (for example `Eq`, `Show`) is decided.

4) `match_list` deprecation
- Policy:
Keep `match_list` as compatibility sugar/macro with warnings; do not keep as permanent core syntax.
- Why:
Avoids bootstrap breakage while moving toward a single generic `match` core.
- Gate to remove:
Generic `match` is stable, macro system can express list-pattern sugar, and stdlib no longer depends on `match_list`.

5) Binder/arrow sugar freeze
- Policy:
Keep multi-binder and arrow syntax experimental until module/import/open and name resolution are frozen.
- Why:
Sugar stability depends on parser, qualification, and diagnostic behavior being stable first.
- Gate to freeze:
Module system contract is frozen and formatter can canonicalize sugar (or canonical desugaring) consistently.

**Implementation Checklist (Gate Tracking)**

1) Canonical modifier authoring form
- Status: In progress.
- Implemented now: compatibility warnings for top-level legacy `(opaque ...)` and `(transparent ...)` forms.
- Remaining to close gate: rewrite stdlib to canonical `def` forms and ship formatter/rewrite support.
- Code paths: `cli/src/driver.rs` (`emit_syntax_compat_warnings`).
- Acceptance checks: `cli/tests/syntax_gate_acceptance.rs` (`legacy_modifier_spellings_emit_compatibility_warnings`, `canonical_def_modifiers_do_not_emit_compatibility_warnings`).

2) Dedicated `String` rollout
- Status: Planned.
- Implemented now: string literals remain `List Nat` for 0.1.
- Remaining to close gate: stabilize typed backend Stage 1, define runtime representation contract, introduce edition-gated migration behavior.
- Code paths: `frontend/src/desugar.rs`, `frontend/src/declaration_parser.rs`.
- Acceptance checks today: none (gate intentionally deferred).

3) Struct/record freeze
- Status: Planned/experimental.
- Implemented now: no freeze; stays experimental sugar.
- Remaining to close gate: finalize desugaring and minimal derivation policy.
- Code paths: `frontend/src/declaration_parser.rs`, `frontend/src/desugar.rs`.
- Acceptance checks today: none (gate intentionally deferred).

4) `match_list` deprecation
- Status: In progress.
- Implemented now: deprecation warning emitted on `match_list` syntax.
- Remaining to close gate: remove stdlib/internal dependency, ensure macro replacement is stable, then remove special-case core form.
- Code paths: `cli/src/driver.rs` (`emit_match_list_warnings`).
- Acceptance checks: `cli/tests/syntax_gate_acceptance.rs` (`match_list_emits_deprecation_warning`).

5) Binder/arrow sugar freeze
- Status: Planned/experimental.
- Implemented now: still experimental, not frozen in 0.1 contract.
- Remaining to close gate: freeze module/import/open contract and formatter canonicalization strategy.
- Code paths: `frontend/src/desugar.rs`, `docs/spec/syntax_contract_0_1.md`.
- Acceptance checks today: none (gate intentionally deferred).

6) Module/import/open contract
- Status: In progress with contract tests.
- Implemented now: explicit `module`, aliased `import`, separate `open`, deterministic ambiguity diagnostics, strict qualified resolution rules.
- Remaining to close gate: full stdlib migration and additional cross-module coverage as syntax expands.
- Code paths: `cli/src/driver.rs`, `frontend/src/elaborator.rs`.
- Acceptance checks: `cli/tests/module_resolution.rs`.

7) Core parser/desugar syntax conformance
- Status: In progress with executable contract checks.
- Implemented now: conformance tests cover reader tokenization, quote token expansion, hole/index behavior, import/open declaration shapes, `app` arity, `match` minimum-case rule, and string/quote term desugaring.
- Remaining to close gate: extend coverage to any newly documented forms as syntax evolves.
- Code paths: `frontend/src/parser.rs`, `frontend/src/declaration_parser.rs`, `frontend/src/desugar.rs`.
- Acceptance checks: `frontend/tests/syntax_contract_conformance.rs`.

**Edition Bump Required If Changed**
- Any change to the tokenization of symbols, integers, strings, or `_`.
- Any change to list/braced/index/quote tokenization or precedence.
- Any change to the surface spelling or arity of core declarations and term forms.
- Any change to macro hygiene scope attachment or `quote`/`quasiquote` behavior.

---

**Known Discrepancies (Code vs. Expected Contract)**

None known after the 2026-02-06 conformance fixes.

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
Likely code locations: `frontend/src/desugar.rs`, `stdlib/prelude_api.lrl`.

5) Add explicit syntax for grouped def modifiers
Justification: current mix of `(def opaque ...)` and `(opaque ...)` is easy to misuse.
Likely code locations: `frontend/src/declaration_parser.rs`.

6) Add module export controls (future)
Justification: current module model exports all names by prefix; explicit export lists may be needed as stdlib scales.
Likely code locations: `frontend/src/declaration_parser.rs`, `cli/src/driver.rs`, `kernel` env policy hooks.
