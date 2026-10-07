#lang typed/racket #:with-refinements
;; Q1 negative (Typed Racket refinements): vhead of an empty vector. Expected: type error.
(require "q01_head_refined.rkt")
(vhead (vector))
