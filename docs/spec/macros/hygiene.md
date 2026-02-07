# Hygiene

LRL uses a "sets of scopes" hygiene algorithm.

## Scopes

When a macro expands, a new `ScopeId` is generated.
- Identifiers introduced by the macro receive this scope.
- Identifiers passed to the macro do *not* receive this scope.
- Resolution looks for identifiers that have a subset of the use-site scopes.

## Breaking Hygiene

`datum->syntax` allows stripping or adding scopes manually to intentionally capture variables.
