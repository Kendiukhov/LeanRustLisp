#lang s-exp turnstile/examples/linear/lin
;; Q10 negative (Turnstile linear language): the token is consumed in both branches and then
;; used again. Expected: rejected before running (linear variable used more than once).
(define (pick [flag : Bool]) Int
  (let ([tok (λ ([x : Int]) (add1 x))])
    (let ([r (if flag (tok 1) (tok 2))])
      (tok r))))
(pick #f)
