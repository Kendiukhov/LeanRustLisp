# Lexical Structure

LRL source files must be UTF-8 encoded.

## Whitespace

Whitespace is defined as any character for which `char::is_whitespace()` returns true (includes spaces, tabs, newlines). Whitespace separates tokens but is otherwise ignored.

## Comments

Comments start with `;` and extend to the end of the line.

```lisp
; This is a comment
(add 1 2) ; Comment at end of line
```

## Identifiers (Symbols)

Symbols are sequences of characters that are NOT:
- Whitespace
- Delimiters: `(`, `)`, `[`, `]`, `{`, `}`
- Quotes: `'`, `` ` ``, `,`

Examples: `foo`, `foo-bar`, `+`, `->`, `Foo.Bar`.

*Note: The symbol `_` is reserved as a "Hole".*

## Literals

### Integers
Currently, only unsigned integers fitting in `usize` are supported by the parser.
Regex: `[0-9]+`

### Strings
Strings are enclosed in double quotes `"`.
Supported escapes:
- `\n` (newline)
- `\r` (carriage return)
- `\t` (tab)
- `\"` (quote)
- `\\` (backslash)

## Delimiters

- `(...)`: Standard lists (S-expressions).
- `{...}`: Braced lists (often used for implicit arguments or blocks, semantically equivalent to lists at parse time).
- `[...]`: Indexing (postfix). `a[b]` parses as `(index a b)`.
