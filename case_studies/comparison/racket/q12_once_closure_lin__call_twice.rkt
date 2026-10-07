#lang s-exp turnstile/examples/linear/lin
;; Q12 negative (Turnstile linear language): a linear function called twice.
;; Expected: rejected before running (linear variable used more than once).
(let ([consume (λ ([x : Int]) (add1 x))])
  (- (consume 5) (consume 6)))
