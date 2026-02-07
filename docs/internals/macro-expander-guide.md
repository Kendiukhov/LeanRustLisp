# Macro Expander Guide

## Overview
Macro expansion happens before elaboration.

## Mechanism
1. The parser produces a `Syntax` tree.
2. The expander traverses the tree.
3. If it encounters a macro, it invokes the macro function (interpreted).
4. Hygiene is maintained by tracking `ScopeId`s on syntax nodes.

## Adding Macros
Macros are defined in standard libraries or user code. The expander must be able to load these definitions (bootstrapping).
