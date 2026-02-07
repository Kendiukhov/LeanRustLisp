# Security Policy

## Reporting Vulnerabilities
Please report security issues via GitHub Security Advisories or email maintainers directly.

## Trusted Base
The `kernel` crate is the critical component for logical soundness. Bugs in `frontend` or `codegen` may cause crashes or wrong output but should not compromise the logical TCB of the verifier itself.
