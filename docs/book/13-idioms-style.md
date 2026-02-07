# Idioms and Style

## Style Guidelines

- **Indent**: 2 spaces.
- **Line Length**: 80-100 characters.
- **Parentheses**: Don't leave dangling parentheses.
  - Good: `(list 1 2 3)`
  - Bad: `(list 1 2 3 )`

## Macro Discipline

Don't use macros just because you can.
- **Use Functions** when possible. They are easier to type-check and debug.
- **Use Macros** for control flow (like `if`, `match`), binding forms, or DSLs.

## Proofs

Keep proofs separate from logic where possible, or use the `Prop` universe to ensure they don't impact runtime performance.
