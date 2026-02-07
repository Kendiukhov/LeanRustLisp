# Name Resolution

LRL allows breaking programs into modules (files) and managing namespaces.

## Scoping Rules

Scopes are lexical. Local variables shadow outer variables.
Definitions in the same module are visible everywhere in that module (order-independent for top-level `def`, though the kernel requires valid dependency ordering).

## Modules and Imports

Each file is a module.
- `use <module>` opens a module, making its definitions available unqualified.
- `use <module> as <alias>` adds a qualified alias.

## Ambiguity

If two opened modules export the same name, using that name unqualified is an error (`AmbiguousName`). You must use the qualified name `Module.name`.
