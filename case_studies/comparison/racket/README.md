# Racket comparison programs

Small, self-contained programs for the properties Q1 to Q12 of the comparison
(`../results_rust_racket.md` has the observed outcome of every program). They cover five
dialects of the Racket ecosystem:

| Dialect | `#lang` line | Package |
|---|---|---|
| Racket | `#lang racket/base` | base distribution |
| Typed Racket | `#lang typed/racket/base` | `typed-racket` |
| Typed Racket + refinements | `#lang typed/racket #:with-refinements` (experimental) | `typed-racket` |
| Cur | `#lang cur` (a dependently typed language implemented with Turnstile+ macros) | `cur` |
| Turnstile lin | `#lang s-exp turnstile/examples/linear/lin` or `.../lin+chan` (a linear lambda calculus implemented with Turnstile macros) | `turnstile-example` |

The run script reports the installed package versions in the results file. To install the
packages: `raco pkg install --auto typed-racket cur turnstile-example`.

## Conventions

- A file `qNN_name.rkt` is a positive program (a correct program that uses the feature);
  `qNN_name__variant.rkt` is a variant, usually a negative one (the property is violated).
  The run script's case list says which files are positive and which are negative, and what
  outcome we expect.
- Plain and Typed Racket negatives are small clients that `require` the positive module.
  Cur negatives are self-contained copies of the positive program with one change.
- Plain and Typed Racket programs print from a `main` submodule; Cur and Turnstile programs
  print the values of their top-level expressions.
- The run script copies the files to a build directory and runs `raco make FILE` (compile and
  type check) and then `racket FILE`, so no `compiled/` directories appear in the repository.

Run everything (Rust and Racket) and regenerate the results table:

```sh
CMP_BUILD_DIR=/some/tmp/dir case_studies/comparison/run_rust_racket.sh
```

## Files

| File | Dialect | Q | Kind | What it shows |
|---|---|---|---|---|
| `q01_head_plain.rkt` | Racket | Q1 | positive | `head` is `car`; nothing is checked before running |
| `q01_head_plain__empty.rkt` | Racket | Q1 | negative | head of `'()`: `car` contract violation at run time |
| `q01_head_typed.rkt` | Typed Racket | Q1 | positive | total `head` on `(Pairof A (Listof A))` (non-emptiness, not a length index) |
| `q01_head_typed__empty.rkt` | Typed Racket | Q1 | negative | head of `'()`: type error |
| `q01_head_refined.rkt` | TR + refinements | Q1 | positive | `vhead` with the dependent precondition `#:pre (v) (< 0 (vector-length v))` |
| `q01_head_refined__empty.rkt` | TR + refinements | Q1 | negative | `(vhead (vector))`: "unable to prove precondition" |
| `q01_head_refined__unrefined.rkt` | TR + refinements | Q1 | negative | the same unchecked `unsafe-vector-ref` in a function with no precondition is accepted: the body is trusted, not verified |
| `q01_head_refined__submodule.rkt` | TR + refinements | Q1 | positive | precondition written as a `Refine` argument type: the call type-checks at module level but the identical call in `module+ main` is rejected |
| `q01_head_cur.rkt` | Cur | Q1 | positive | indexed family `Vect A n`; total `head` on `(Vect A (s n))` with a large-elimination motive |
| `q01_head_cur__empty.rkt` | Cur | Q1 | negative | `(head Nat z (vnil Nat))`: type error |
| `q01_head_cur__any_length.rkt` | Cur | Q1 | negative | a `head` on `(Vect A n)` for every `n`: the nil case does not type-check |
| `q02_append_plain.rkt` | Racket | Q2 | positive | the length law as a dependent contract (`->i`), checked on every call |
| `q02_append_plain__off_by_one.rkt` | Racket | Q2 | negative | wrong implementation: the contract blames it at run time |
| `q02_append_typed.rkt` | Typed Racket | Q2 | positive | `append` has type `(Listof A) ... -> (Listof A)`: the true claim "3 elements" is rejected |
| `q02_append_refined.rkt` | TR + refinements | Q2 | positive | `vappend` whose result type says length = sum; the caller's claim "length 3" is checked |
| `q02_append_refined__wrong_len.rkt` | TR + refinements | Q2 | negative | caller claims length 2: type error |
| `q02_append_refined__off_by_one.rkt` | TR + refinements | Q2 | negative | implementation allocates one slot too many: type error |
| `q02_append_refined__vector_append.rkt` | TR + refinements | Q2 | positive | correct implementation through library `vector-append`, whose type has no length information: rejected |
| `q02_append_cur.rkt` | Cur | Q2 | positive | `append : Vect A n -> Vect A m -> Vect A (plus n m)` |
| `q02_append_cur__wrong_len.rkt` | Cur | Q2 | negative | result used as a `(Vect Nat 2)`: type error |
| `q02_append_cur__drop_elem.rkt` | Cur | Q2 | negative | cons case forgets the element: type error |
| `q03_reverse_involution_plain.rkt` | Racket | Q3 | positive | run-time check on chosen inputs only |
| `q03_reverse_involution_plain__buggy.rkt` | Racket | Q3 | negative | wrong reverse: found by the run-time check |
| `q03_reverse_involution_refined.rkt` | TR + refinements | Q3 | positive | the statement `(= r l)` on lists is not a valid refinement (linear integer constraints only) |
| `q03_reverse_involution_cur.rkt` | Cur | Q3 | positive | ntac proof of `rev (rev l) = l` (lemmas `app-nil-r`, `app-assoc`, `rev-app-distr`) |
| `q03_reverse_involution_cur__buggy.rkt` | Cur | Q3 | negative | same proof scripts for a reverse that drops elements: a proof step fails at compile time |
| `q04_evidence_tokens_typed.rkt` | Typed Racket | Q4 | positive | the evidence token is a run-time value and a run-time argument; the program checks this and exits with an error |
| `q04_evidence_tokens_typed__forge.rkt` | Typed Racket | Q4 | negative | a client cannot construct the token (constructor not exported): unbound identifier |
| `q05_single_use_channel_plain.rkt` | Racket | Q5 | positive | single use enforced by a run-time flag |
| `q05_single_use_channel_plain__reuse.rkt` | Racket | Q5 | negative | second send: run-time error |
| `q05_single_use_channel_typed.rkt` | Typed Racket | Q5 | positive | the same with types (no linear/affine types) |
| `q05_single_use_channel_typed__reuse.rkt` | Typed Racket | Q5 | negative | second send type-checks; run-time error |
| `q05_single_use_channel_lin.rkt` | Turnstile lin | Q5 | positive | `lin+chan`: the receiving end `(InChan Int)` is linear and is threaded through `channel-get` |
| `q05_single_use_channel_lin__reuse.rkt` | Turnstile lin | Q5 | negative | receive twice from the same variable: "linear variable used more than once" |
| `q06_typestate_plain.rkt` | Racket | Q6 | positive | state checked at run time |
| `q06_typestate_plain__send_after_close.rkt` | Racket | Q6 | negative | send after close: run-time error |
| `q06_typestate_typed.rkt` | Typed Racket | Q6 | positive | typestate with a polymorphic struct `(Chan S)` |
| `q06_typestate_typed__send_after_close.rkt` | Typed Racket | Q6 | negative | send after close: type error |
| `q07_protocol_length_plain.rkt` | Racket | Q7 | positive | message counter checked at run time; generic `send-all` |
| `q07_protocol_length_plain__too_many.rkt` | Racket | Q7 | negative | third send on a 2-message channel: run-time error |
| `q07_protocol_length_typed.rkt` | Typed Racket | Q7 | positive | Peano-indexed `(Chan N)` for a written-out sequence of sends |
| `q07_protocol_length_typed__too_many.rkt` | Typed Racket | Q7 | negative | third send: type error |
| `q07_protocol_length_typed__too_few.rkt` | Typed Racket | Q7 | negative | close after one send: type error |
| `q07_protocol_length_typed__send_all.rkt` | Typed Racket | Q7 | positive | a generic "send every element of a length-N vector over a (Chan N)" is rejected: occurrence typing does not refine the type variable N |
| `q08_macro_hygiene.rkt` | Racket | Q8 | positive | template binder `tmp` does not capture the user's `tmp`; a template's free reference to `helper` resolves at the macro's definition site |
| `q08_macro_plain_ops.rkt` | Racket | Q8 | positive | `def-unit` macro generating a struct and an `-add` operation |
| `q08_macro_plain_ops__mix_units.rkt` | Racket | Q8 | negative | adding Seconds to Meters: run-time contract error from the generated accessor |
| `q08_macro_typed_ops.rkt` | Typed Racket | Q8 | positive | the same macro generating typed code (syntax-parse) |
| `q08_macro_typed_ops__mix_units.rkt` | Typed Racket | Q8 | negative | adding Seconds to Meters: type error in the generated operation's use |
| `q09_distinct_boxes.rkt` | Racket | Q9 | positive | two mutable references to two different boxes |
| `q09_distinct_boxes_typed.rkt` | Typed Racket | Q9 | positive | the same with types |
| `q09_aliasing_boxes.rkt` | Racket | Q9 | negative | two live aliases of one box, both written: accepted |
| `q09_aliasing_boxes_typed.rkt` | Typed Racket | Q9 | negative | the same with types: accepted |
| `q10_consume_both_branches_plain.rkt` | Racket | Q10 | positive | the run-time-flag channel used in both branches |
| `q10_consume_both_branches_plain__use_after.rkt` | Racket | Q10 | negative | used again after the branches: run-time error |
| `q10_consume_both_branches_lin.rkt` | Turnstile lin | Q10 | positive | a linear value consumed in both branches of `if` |
| `q10_consume_both_branches_lin__one_branch.rkt` | Turnstile lin | Q10 | positive | consumed in one branch only: rejected, because `lin` is linear (Rust, being affine, accepts this program shape) |
| `q10_consume_both_branches_lin__drop.rkt` | Turnstile lin | Q10 | positive | the same with an explicit `(drop tok)` in the other branch: accepted |
| `q10_consume_both_branches_lin__use_after.rkt` | Turnstile lin | Q10 | negative | used again after the `if`: rejected |
| `q11_inplace_vector_reverse.rkt` | Racket | Q11 | positive | `vector-reverse!` returns the same object (`eq?`); list `reverse` allocates |
| `q11_inplace_vector_reverse__alias.rkt` | Racket | Q11 | negative | in-place reverse while an alias is live: accepted, the alias observes it |
| `q12_once_closure_plain.rkt` | Racket | Q12 | positive | "at most once" by a run-time wrapper |
| `q12_once_closure_plain__call_twice.rkt` | Racket | Q12 | negative | second call: run-time error |
| `q12_once_closure_typed.rkt` | Typed Racket | Q12 | positive | the same wrapper with a type (no once-only function types) |
| `q12_once_closure_typed__call_twice.rkt` | Typed Racket | Q12 | negative | second call type-checks; run-time error |
| `q12_once_closure_lin.rkt` | Turnstile lin | Q12 | positive | a linear function `(-o Int Int)` called once |
| `q12_once_closure_lin__call_twice.rkt` | Turnstile lin | Q12 | negative | called twice: "linear variable used more than once" |
| `q12_once_closure_lin__unrestricted_capture.rkt` | Turnstile lin | Q12 | negative | captured by an unrestricted `(λ ! ...)`: "linear variable may not be used by unrestricted function" |

## What the Racket dialects could and could not do (observed; see the results table)

- Plain Racket checks nothing before running. Every property is either a run-time check
  (contracts, flags, wrappers; Q1, Q2, Q3, Q5 to Q8, Q10, Q12) or not enforced at all (two live
  mutable aliases, Q9; mutation observed through an alias, Q11). Its macros are hygienic for
  template binders and for template references to global names (Q8).
- Typed Racket rejects before running: head of an empty list (Q1, via a non-empty list type),
  wrong-state calls (Q6), too many / too few sends for a written-out sequence (Q7), mixing
  macro-generated unit types (Q8). Rejected although correct: the claim that appending a
  2-list and a 1-list gives a 3-list (Q2; `append` is typed `(Listof A) ... -> (Listof A)`) and a
  generic "send every element of a length-N vector over a (Chan N)" (Q7; after the test on the
  vector the channel still has type `(Chan N)`). Accepted by the type checker and caught only at
  run time: reuse of a channel (Q5) and a second call of a once-only closure (Q12). Not caught
  at all: two live aliases of a mutable box (Q9). Evidence values are ordinary run-time values
  (Q4); a module can make them unforgeable by not exporting the constructor.
- Typed Racket's experimental refinement types check length facts about vectors: a total `vhead`
  (Q1) and a length-indexed `vappend` (Q2), including wrong claims by callers and an off-by-one
  implementation. Limits observed: the refinement logic is linear integer arithmetic, so list
  equality (Q3) cannot be stated; `unsafe-vector-ref` is not verified, so the body of a refined
  function is trusted; library functions without refined types (`vector-append`) cannot be
  used to meet a refined result type; and a precondition written as a `Refine` argument type
  is not satisfied inside a `module+ main` submodule although the same call type-checks at
  module level.
- Cur (dependent types built from Turnstile+ macros) expresses Q1, Q2 and Q3 with checked
  proofs: an indexed vector with a total head, append with length `plus n m`, and an ntac proof
  that reverse is an involution; the corresponding negatives are rejected when the module is
  compiled. In this installation (Racket 9.3, cur commit `98f7218`), `by-intros` followed by
  `by-induction` fails with "unbound identifier", also in Cur's own test
  `cur-test/cur/tests/ntac/software-foundations/Lists.rkt`; the proofs here therefore introduce
  one variable at a time with `by-intro`. The error for the failed proof in
  `q03_reverse_involution_cur__buggy.rkt` has no source location. Q4 (run-time representation of
  Cur terms) was not examined.
- The Turnstile `lin` example languages enforce linearity before running: a linear channel end
  cannot be reused (Q5), a linear function cannot be called twice or captured by an unrestricted
  function (Q12), and a linear value must be consumed in both branches of an `if` (Q10). Because
  the discipline is linear rather than affine, a value consumed in one branch and ignored in the
  other is rejected; with an explicit `(drop tok)` in the other branch it is accepted. In
  `lin`, `(begin (if flag (tok 1) 0) (tok 2))` made the example language itself fail with an
  internal contract error (`linear-mode-scope: contract violation`); that program is not part
  of the corpus.
- No Racket dialect here rejects two live mutable aliases (Q9) or mutation through an alias
  (Q11): there is no borrow checking.

## Audit note

Every outcome stated above was observed in the session that wrote this file (2026-10-05) by
running `CMP_BUILD_DIR=<tmp> case_studies/comparison/run_rust_racket.sh` (113 of 113 cases as
expected at the time; 114 of 114 after the Rust `zero_divisor` case was added in a later session; Racket v9.3 [cs], packages as listed in `../results_rust_racket.md`). The packages
were installed with `raco pkg install --auto --batch --no-docs cur` and
`... turnstile-example` (each finished in under a minute) after `typed-racket` had been
installed earlier. The `by-intros` failure in Cur's own test was reproduced by copying
`cur-test/cur/tests/ntac/software-foundations/` and `rackunit-ntac.rkt` to a temporary
directory and running `raco make Lists.rkt` there ("l1: unbound identifier in module",
`Lists.rkt:191:16`). The type of `unsafe-vector-ref` was read in
`typed-racket-lib/typed-racket/base-env/base-env-indexing-abs.rkt`. The internal error of the
`lin` example language and the accepted `(drop tok)` program were observed with hand-run
`raco make` on scratch files outside the repository.
