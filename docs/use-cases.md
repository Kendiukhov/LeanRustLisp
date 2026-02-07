# Use Cases

Why LeanRustLisp? Here are the problems we solve.

<div class="grid cards" markdown>

-   __Verified Systems Programming__

    **Problem**: C/C++ are unsafe. Rust is safe but hard to verify formally.
    **Solution**: LRL allows you to write low-level code with integrated proofs of correctness.
    **Status**: _Planned_

-   __Safe High-Performance Infrastructure__

    **Problem**: High-performance code often requires `unsafe` in Rust.
    **Solution**: Dependent types can express invariants (like buffer sizes or state machine transitions) that remove the need for runtime checks without `unsafe`.
    **Status**: _Early Access_

-   __DSLs and Tooling__

    **Problem**: Creating a new language is hard.
    **Solution**: LRL's Racket-like macro system makes it a "language for building languages."
    **Status**: _Available_

-   __Security-Sensitive Capability Code__

    **Problem**: Access control is often implicit.
    **Solution**: Linear capability tokens (`IO`, `Network`) enforce security policies at the type level.
    **Status**: _Designing_

-   __Proof-Carrying APIs__

    **Problem**: APIs rely on documentation for constraints ("must call init first").
    **Solution**: Types encode the protocol. A function strictly cannot be called in the wrong state.
    **Status**: _Available_

-   __Research & Education__

    **Problem**: PL research languages are often slow or garbage collected.
    **Solution**: LRL provides a playground for type theory that compiles to standard, fast systems code.
    **Status**: _Available_

</div>
