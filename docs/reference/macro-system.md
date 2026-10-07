# Macro System

LRL provides template macros that operate on syntax objects (`Syntax`):

```lisp
(defmacro name (p1 ... pn) template)
```

A call `(name a1 ... an)` (exactly `n` arguments) is replaced by `template` with every symbol
`pi` replaced by the argument syntax `ai`; the result is expanded again. Quasiquote
(`` ` ``, `,`, `,@`) may be used inside templates to build syntax. Nothing is evaluated at macro
time: there are no conditionals, no pattern matching on arguments and no syntax primitives.
The full specification is `docs/spec/macro_system.md`.

## Staging

Macro expansion happens **before** desugaring and type checking. It needs no interpreter: it is
substitution into templates. Macro output is ordinary surface syntax and goes through the whole
pipeline (elaboration, kernel, MIR), so a macro cannot produce anything that could not be written
by hand.

## Hygiene

Hygiene covers **local binders**:
- Syntax introduced by a macro template is marked with a fresh scope for each call.
- Arguments passed to a macro keep their original scopes.

So a binder introduced by a template does not capture a variable of the caller, and a reference
introduced by a template does not resolve to a local binder of the caller.

Macro names and global names (definitions, constructors, inductive types) are **not** hygienic:
they are resolved by name where the macro is used. There is no API to break hygiene on purpose
(no `datum->syntax`). See `docs/spec/macros/hygiene.md`.

## Expansion Order

Macros are expanded **outside-in** (top-down); the arguments of a macro call are not expanded
before the call (they are expanded when the instantiated template is expanded). Expansion is
bounded (number of invocations per top-level form, nesting depth) and repeated identical calls are
reported as cycles.

## Determinism

Macro expansion is deterministic. The same input source code produces the same output syntax
tree.
