# Rust comparison programs

Small, self-contained Rust programs. Each one shows one property from the comparison
(Q1 to Q12 in `../results_rust_racket.md`) in stable Rust, with no external crates and no
verifier. Every file is compiled directly with `rustc --edition 2021`.

Variants live in the same file as the positive program. They are switched on with
`rustc --cfg <variant>`, so a variant differs from its positive by the guarded lines only.
The header comment of each file lists its variants and the expected outcome of each; the run
script's case list says which variants are positive (a correct program that uses the feature)
and which are negative (the property is violated).

Run everything (Rust and Racket) and regenerate the results table:

```sh
CMP_BUILD_DIR=/some/tmp/dir case_studies/comparison/run_rust_racket.sh
```

Or compile one case by hand, outside the repository:

```sh
rustc --edition 2021 --cfg reuse -o /tmp/q05 case_studies/comparison/rust/q05_single_use_channel.rs
```

| File | Property | Variants |
|---|---|---|
| `q01_head_const_generics.rs` | Q1 total `head` on `[T; N]` via an associated-const assertion. The check happens after monomorphization: a full build rejects N = 0, but a check-only build (`--emit=metadata`, like `cargo check`) accepts it. | `empty`, `plain_empty`, `succ_type` |
| `q01_head_typelevel.rs` | Q1 length-indexed vector over type-level Peano numerals. Its representation is computed by a generic associated type, and `head` is a field access with no run-time check. | `empty` |
| `q02_append_const_generics.rs` | Q2 limit probe: `-> [T; N + M]` is rejected on stable (needs `generic_const_exprs`). | none |
| `q02_append_typelevel.rs` | Q2 `append : Vect<T,N> -> Vect<T,M> -> Vect<T,N+M>`, with type-level addition as an associated type. | `wrong_len`, `drop_elem` |
| `q03_reverse_involution.rs` | Q3: not expressible in rustc. Shows the closest substitute, a run-time assertion; a buggy `reverse` still compiles. | `buggy` |
| `q04_zero_sized_proofs.rs` | Q4: evidence tokens and type-level indices are zero-sized (`size_of` = 0, asserted by the program). The LLVM IR of a function that takes an evidence argument has no parameter for it. Forging the evidence outside its module and reading a type-level length as a value are rejected (E0423). Dividing by 0 needs evidence from `check_nonzero(0)`, a run-time check that returns `None`: the program stops at run time (the token is not tied to the divisor's value in the type). | `forge`, `zero_divisor`, `index_at_runtime` |
| `q05_single_use_channel.rs` | Q5: a channel consumed by `send`; reuse is rejected (E0382). | `reuse` |
| `q06_typestate.rs` | Q6 typestate (`Chan<Open>` / `Chan<Closed>`): a wrong-state call is rejected (E0599). | `send_after_close`, `close_twice` |
| `q07_protocol_length.rs` | Q7: `Chan<N>` counts the remaining messages with type-level Peano numerals. A generic `send_vec` sends a `Vect<u64, N>` over a `Chan<N>`. Dropping a channel early is accepted, because Rust is affine. | `too_many`, `too_few`, `len_mismatch`, `skip_send`, `abandon` |
| `q07_protocol_const_generics.rs` | Q7 limit probe: `Chan<{N - 1}>` is rejected on stable. | none |
| `q08_macro_hygiene.rs` | Q8: a `macro_rules!` macro that generates typed newtype operations; the template binder `tmp` does not capture the user's `tmp`. | `mix_units` |
| `q08_macro_global_names.rs` | Q8: mixed-site hygiene. An unqualified item name in a template resolves at the use site; `$crate::` pins it to the definition site. | none |
| `q09_two_mut_refs.rs` | Q9: two live `&mut` to one variable are rejected (E0499); non-overlapping ones are accepted (NLL). | `alias_call`, `alias_live` |
| `q10_consume_both_branches.rs` | Q10: a value moved in both arms of `if` and of `match` is accepted; using it afterwards is rejected (E0382). Moving it in one arm only is also accepted (affine: the value is dropped on the other path). | `use_after`, `one_branch` |
| `q11_inplace_reverse.rs` | Q11: `Vec::reverse` keeps the buffer pointer, also behind `fn(Vec<T>) -> Vec<T>`. Mutation under a live shared borrow (E0502) and use after move (E0382) are rejected. | `shared_alias`, `use_after_move` |
| `q12_fnonce_twice.rs` | Q12: an `FnOnce` closure called twice is rejected (E0382), passing it where `Fn` is required is rejected (E0525), and a loop body that moves a value from outside the loop is rejected (E0382, "value moved here, in previous iteration of loop"). | `call_twice`, `as_fn`, `in_loop` |

What stable Rust cannot do here (observed, see the results table):

- Arithmetic on const generic parameters in types (`[T; N + M]`, `Chan<{N - 1}>`). Q2 and Q7
  therefore use type-level Peano numerals encoded with traits instead of const generics.
- State or check a proof such as `reverse(reverse(v)) == v` (Q3). This needs an external
  verifier such as Verus or Creusot, which this comparison deliberately does not install.
- Force a resource to be used *exactly* once. Rust's ownership is affine: a value can always
  be dropped, so the `abandon` variant of Q7 and the `one_branch` variant of Q10 compile.
- Reject a const-generic precondition in a check-only build: the `N > 0` assertion of
  `q01_head_const_generics.rs` is evaluated after monomorphization, so `--emit=metadata`
  (like `cargo check`) accepts the `empty` variant that a full build rejects.

Audit note: the error codes and outcomes above were observed in the session that last edited
this file (2026-10-05) with rustc 1.78.0, by running `case_studies/comparison/run_rust_racket.sh`
(all Rust cases as expected; see `../results_rust_racket.md`).
