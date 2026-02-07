# Kernel Architecture Guide

## Overview
The `kernel` crate is the Trusted Computing Base (TCB).

## Key Modules
- `ast.rs`: Core term definitions (`Term`, `Level`).
- `checker.rs`: Type checker and definitional equality (`def_eq`).
- `nbe.rs`: Normalization by Evaluation (the engine for `def_eq`).
- `inductives.rs`: Inductive type validity checks (positivity, universe levels).

## Debugging
Use `LRL_DEFEQ_FUEL` to adjust the fuel limit if the kernel seems to hang (which implies a non-terminating reduction or huge term).
