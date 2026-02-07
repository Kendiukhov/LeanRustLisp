# Community & Trust

## Trusted Computing Base (TCB)

In LRL, we distinguish between **Trusted** and **Untrusted** code to minimize the surface area for critical bugs.

-   **Trusted**: `kernel` crate. This is the only code that must be correct for the logical soundness of proofs.
-   **Untrusted**: `frontend`, `elaborator`, `codegen`. Bugs here may cause compile errors or crashes, but (ideally) strictly cannot produce a false proof that passes the kernel.

## Trust Guarantees

-   **P1-P3**: Validated by Kernel. Logic is sound relative to CIC.
-   **P4**: Validated by Borrow Checker. Memory is safe (no use-after-move).
-   **Safety**: We do not use `unsafe` in the generated Rust code unless explicitly opted-in via FFI or Unsafe blocks.

## Reporting Issues

If you find a soundness bug (e.g., you can prove `False`), please report it immediately!

-   **GitHub Issues**: [Open an Issue](https://github.com/Kendiukhov/LeanRustLisp/issues)
-   **Security**: See [Security Policy](dev/security.md)

## Join Us

-   **GitHub Discussions**: Ask questions and share ideas.
-   **Contribution**: See our [Contributing Guide](dev/contributing.md).

We welcome all contributors interested in type theory, Rust, and compiler design.
