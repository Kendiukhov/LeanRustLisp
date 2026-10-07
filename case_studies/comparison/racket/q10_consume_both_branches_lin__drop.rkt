#lang s-exp turnstile/examples/linear/lin
;; Q10 (Turnstile linear language): the program of __one_branch with an explicit `(drop tok)` in
;; the branch that does not use the token. Every path now consumes `tok` exactly once, so the
;; linear checker accepts it. The module prints (pick #f) = 0.
(define (pick [flag : Bool]) Int
  (let ([tok (λ ([x : Int]) (add1 x))])
    (if flag (tok 1) (begin (drop tok) 0))))
(pick #f)
