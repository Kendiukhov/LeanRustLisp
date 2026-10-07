#lang racket/base
;; Q1 negative (plain Racket): head of the empty list. Expected: accepted by the expander,
;; run-time error.
(require "q01_head_plain.rkt")
(printf "head = ~a\n" (head '()))
