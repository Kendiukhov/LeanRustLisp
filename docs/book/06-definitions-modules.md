# Definitions and Modules

## Definitions

You've already seen `def`.

```lisp
(def name type value)
```

Definitions are opaque if you mark them as `opaque` (future feature), but by default, they are transparent—the type checker can unfold them to see their value.

### Naming Conventions

- **Types/Inductives**: CamelCase (e.g., `Nat`, `List`, `MyType`).
- **Functions/Values**: kebab-case (e.g., `add`, `is-valid`, `my-function`).
- **Constructors**: kebab-case or CamelCase depending on preference (stdlib usually uses lowercase for constructors like `zero`, `succ`, `true`, `false`).

## Modules (Planned)

LRL has a preliminary concept of modules based on files.

- Each file is a module.
- `prelude` is implicitly imported.

*Note: The module system is currently under active development. Expect changes here.*

## The Standard Library

The standard library is located in `stdlib/`.

- `stdlib/prelude.lrl`: The default environment.
- `stdlib/prelude_typed.lrl`: A typed variant used for compilation.

You can inspect these files to see how basic types like `Nat`, `Bool`, `Option` are defined.
