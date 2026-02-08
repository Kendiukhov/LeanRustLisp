# Stdlib Suite

This directory contains standalone `.lrl` programs intended to exercise the current standard library surface aggressively:

- `core_bool/`: boolean combinators and conditional helpers (`not`, `and`, `or`, `xor`, `implies`, `if_bool`, `if_nat`)
- `core_nat/`: Nat arithmetic/comparison helpers (`add`, `nat_pred`, `nat_sub`, `nat_is_zero`, `nat_le`, `nat_lt`, `nat_eq`, `nat_ge`, `nat_gt`)
- `core_float/`: Float16 helpers and arithmetic (`float_from_bits`, `float_to_bits`, `+f`, `-f`, `*f`, `/f`)
- `data_list/`: list algorithms (`append`, `length`, `map`, `foldl`, `foldr`, `reverse`, `filter`) including edge and stress-style compositions
- `prelude_platform/`: prelude-level constructors/helpers (`Comp`, `Eq`, print helpers, indexing APIs, interior mutability markers, borrow surface)

Notes:

- Each file is intentionally small and focused.
- Most files define `entry` as a quick smoke target for compile/execute workflows.
- Some files are compile-surface coverage tests (e.g. API wrappers over unsafe/platform primitives).
