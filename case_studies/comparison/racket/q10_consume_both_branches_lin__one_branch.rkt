#lang s-exp turnstile/examples/linear/lin
;; Q10 (Turnstile linear language): the token is consumed in one branch and ignored in the
;; other. An affine system (Rust, LRL) accepts this; `lin` is linear (every linear variable must
;; be used exactly once on every path), so it is expected to be rejected.
(define (pick [flag : Bool]) Int
  (let ([tok (λ ([x : Int]) (add1 x))])
    (if flag (tok 1) 0)))
(pick #f)
