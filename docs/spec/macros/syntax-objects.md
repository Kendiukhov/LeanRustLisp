# Syntax Objects

Macros operate on `Syntax` objects, not raw S-expressions.

## Structure

```rust
struct Syntax {
    kind: SyntaxKind,
    span: Span,
    scopes: Vec<ScopeId>, // Hygiene info
}
```

## kinds

- `Symbol(String)`
- `List(Vec<Syntax>)`
- `Int(usize)`
- `String(String)`
