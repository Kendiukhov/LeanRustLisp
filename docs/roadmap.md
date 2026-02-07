# Roadmap

Current status and future plans for LeanRustLisp.

## Status Matrix

| Feature | Status | Notes |
| :--- | :--- | :--- |
| **Core Kernel** | :white_check_mark: **Done** | CIC, Universes, Inductives verified. |
| **MIR & NLL** | :white_check_mark: **Done** | Borrow checker and Mid-level IR working. |
| **Macro System** | :white_check_mark: **Done** | Hygiene, staging, quasiquotes implemented. |
| **Typed Backend** | :construction: **Stage 1** | Compiles basic constructs to Rust. |
| **Closures** | :memo: **Planned** | Closure conversion and lambda lifting. |
| **Interpreter** | :hourglass: **Later** | Pure interpreter for scripts. |
| **Package Manager** | :hourglass: **Later** | Dependency management. |

## Milestones

### Phase 1: Foundation (Completed)
- [x] Syntax & Parser
- [x] Core Type Checker (Kernel)
- [x] Basic Elaborator

### Phase 2: System (Current)
- [x] Borrow Checking
- [x] Macro Expander
- [ ] Stdlib (List, Nat, String)
- [ ] Effects System (IO)

### Phase 3: Polish (Next)
- [ ] Language Server (LSP)
- [ ] Generics / Polymorphism in Backend
- [ ] Optimizations

[View GitHub Projects](https://github.com/users/Kendiukhov/projects/){ .md-button .md-button--primary }
