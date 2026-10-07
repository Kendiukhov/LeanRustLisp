#lang s-exp turnstile/examples/linear/lin
;; Q10 (Turnstile linear language `lin`, from the turnstile-example package): a linear value
;; (here a linear function, type (-o Int Int)) consumed in both branches of an `if` is accepted:
;; the checker requires both branches to consume the same linear variables.
;; Negatives: __one_branch (consumed in one branch only: rejected, because `lin` is LINEAR,
;; not affine), __use_after (used again after the `if`: rejected).
;; The module prints (pick #f) = 3.
(define (pick [flag : Bool]) Int
  (let ([tok (λ ([x : Int]) (add1 x))])
    (if flag (tok 1) (tok 2))))
(pick #f)
