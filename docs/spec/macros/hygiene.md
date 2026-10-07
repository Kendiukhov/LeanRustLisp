# Hygiene

LRL uses a simplified "sets of scopes" algorithm for **local binders**. Names of macros and of
global items (definitions, inductive types, constructors) are not covered by it.

## Scopes

- Each macro invocation creates a fresh `ScopeId` (`Expander::new_scope`).
- Syntax introduced by the macro template (every node of the template except the substituted
  arguments) receives this scope. Macro arguments are substituted unchanged and keep their own
  scopes.
- Spans of template-introduced nodes are remapped to the macro call site; arguments keep their
  original spans.

## Resolution of local binders (desugaring)

The desugarer resolves each identifier that refers to a local binder (`lam`, `pi`, `let`, `fix`,
`match` case variables) by name and scope set:

- a reference can see a binder when the binder's (normalised) scope set is a
  subset of the use-site scopes (the reference's scope set); among the visible binders of that
  name, the one with the largest scope set wins (ties are broken deterministically);
- a reference that carries scopes never resolves to an unscoped binder (no fallback from
  macro-introduced references to user binders), and an unscoped binder is visible only to
  unscoped references.

Consequently a binder introduced by a template does not capture a user's variable passed as an
argument, and a template's reference does not capture a user's local binder of the same name.

## What is not hygienic

- **Macro names** are resolved by bare name in the module where the call is expanded
  (`Expander::resolve_macro`: that module's macros, then its imported macro modules). A local
  binder that has the same name as a macro is shadowed by the macro when used in head position,
  and a macro template that calls another macro uses the call site's definition of that name.
- **Global names** in a template (definitions, constructors, inductive types) are ordinary free
  identifiers after expansion; the elaborator resolves them in the call site's module.

There is no way to break or bend hygiene explicitly: macros have no `datum->syntax`, no access to
scopes, and no gensym; a template is instantiated by substitution only (see
`docs/spec/macro_system.md`).
