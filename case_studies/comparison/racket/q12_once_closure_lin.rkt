#lang s-exp turnstile/examples/linear/lin
;; Q12 (Turnstile linear language `lin`): a lambda has the linear function type (-o Int Int)
;; unless it is marked unrestricted with `λ !`; a linear function must be called exactly once.
;; Negatives: __call_twice (called twice), __unrestricted_capture (captured by an unrestricted,
;; i.e. repeatable, function). The module prints 6.
(let ([consume (λ ([x : Int]) (add1 x))])
  (consume 5))
