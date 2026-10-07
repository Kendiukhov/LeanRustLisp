#lang s-exp turnstile/examples/linear/lin
;; Q12 negative (Turnstile linear language): an unrestricted function (`λ !`, callable any number
;; of times) captures the linear function `consume`. Expected: rejected before running.
;; (Rust's E0525 for an FnOnce closure passed where Fn is required is the analogous check.)
(let ([consume (λ ([x : Int]) (add1 x))])
  (let ([many (λ ! ([y : Int]) (consume y))])
    (many 1)))
