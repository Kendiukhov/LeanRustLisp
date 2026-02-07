# FAQ

## Why is inference limited?
Full type inference for dependent types is undecidable. LRL relies on bidirectional typing, which requires annotations in top-level definitions and some other places, but infers types for most expressions.

## Why can't types depend on partial code?
If a type depends on a function that loops forever, the type checker would loop forever. Logic requires total functions.

## Why does borrow checking exist if we transpile to Rust?
LRL's borrow checker runs on MIR *before* codegen. It mirrors Rust's rules to ensure that the generated Rust code is valid and safe, providing error messages in terms of LRL source code rather than confusing Rust compiler errors.

## How do I do dynamic stuff?
Use the `Dyn` type or `Any`. We support a "dynamic backend" which is more permissive, but the "typed backend" enforces static discipline.
