# Elaborator Guide

## Overview
The `elaborator` in `frontend/src/elaborator.rs` converts surface syntax into kernel terms.

## Responsibilities
1. **Name Resolution**: Managing scopes and resolving identifiers.
2. **Type Inference**: Generating metavariables (`?m`) for holes and solving them via unification.
3. **Implicit Arguments**: Inserting code for implicit arguments.
4. **Desugaring**: Converting `match` to `Rec` applications.

## Unification
Bidirectional unification is used. If unification fails, an error is reported with distinct expected vs actual types.
