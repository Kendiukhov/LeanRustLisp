# Macro System

LRL provides a hygienic macro system where macros operate on AST nodes (`Syntax`).

## Staging

Macro expansion happens **before** desugaring and type checking.
Macros are executed in a separate interpreter/evaluator environment, but currently share the same process.

## Hygiene

LRL macros are hygienic by default.
- Variables introduced by a macro are marked with a fresh "scope".
- Variables passed to a macro retain their original scopes.

This prevents accidental variable capture ("the Lisp-1 problem").

### Breaking Hygiene

A macro can intentionally break hygiene by constructing raw symbols without scopes using `(datum->syntax quote-syntax 'symbol)`. (API subject to change).

## Expansion Order

Macros are expanded **outside-in** (top-down), but arguments to macros are not expanded before the macro is called (standard Lisp macro behavior).

## Determinism

Macro expansion MUST be deterministic. The same input source code must produce the same output syntax tree.
