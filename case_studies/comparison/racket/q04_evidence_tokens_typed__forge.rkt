#lang typed/racket/base
;; Q4 negative (Typed Racket): build the evidence token directly instead of obtaining it from
;; `check-nonzero`. The constructor is not exported. Expected: rejected before running
;; (unbound identifier).
(require "q04_evidence_tokens_typed.rkt")
(div-with-proof 1 0 (IsNonZero))
