#lang typed/racket/base
;; Q1 negative (Typed Racket): head of the empty list. Expected: rejected by the type checker.
(require "q01_head_typed.rkt")
(head '())
