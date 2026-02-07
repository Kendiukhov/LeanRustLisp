# Total vs Partial

## Totality
Terms in `Type` arguments must be total to ensure type checking terminates.
The kernel enforces termination (structural/well-founded).

## Partial
Functions marked `partial` can loop.
They return a computation type (e.g. `Comp A` or `IO A`) and cannot be unfolded by Refinement types or DefEq.
