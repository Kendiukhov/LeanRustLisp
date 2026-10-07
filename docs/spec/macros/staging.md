# Staging

Macros are expanded in a separate stage, on syntax, before desugaring, elaboration and type
checking.

## Invocation

Macros are expanded by the frontend's `Expander` (`frontend/src/macro_expander.rs`). There is no
macro-time interpreter or VM: a macro is a template, `(defmacro name (p1 ... pn) template)`. A
call `(name a1 ... an)` must supply exactly `n` arguments; it is replaced by the template in which
every symbol `pi` is replaced by the argument syntax `ai` (other template nodes get the call's
fresh hygiene scope), and the result is expanded again. `quasiquote` / `unquote` /
`unquote-splicing` in a template are processed during that re-expansion; they build syntax, not
runtime values.

Macro expansion cannot run code: it has no conditionals, no pattern matching on its arguments, no
access to types, the kernel, the environment of definitions, or I/O. Macros are made available by
`defmacro` in the same file or by `(import-macros "path")`; nothing else needs to exist at macro
time.
