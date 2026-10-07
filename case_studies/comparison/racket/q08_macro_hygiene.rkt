#lang racket/base
;; Q8 (plain Racket): hygiene of template binders and of template references to global names.
;;
;; `with-tmp` binds `tmp` in its template and evaluates the user's expression in that scope:
;; the user's `tmp` is not captured (result 101, not 2).
;; `call-helper` is defined in submodule `lib` and mentions `helper` unqualified; invoked
;; from submodule `user`, which defines its own `helper`, it still calls lib's `helper`:
;; Racket resolves free identifiers of a template at the macro's definition site.

(define-syntax-rule (with-tmp e)
  (let ([tmp 1]) (+ e tmp)))

(module lib racket/base
  (provide call-helper)
  (define (helper) "lib helper (definition site)")
  (define-syntax-rule (call-helper) (helper)))

(module user racket/base
  (require (submod ".." lib))
  (provide run)
  (define (helper) "user helper (use site)")
  (define (run) (printf "(call-helper) -> ~a\n" (call-helper))))

(require 'user)

(module+ main
  (define tmp 100)
  (printf "(with-tmp tmp) = ~a (101 = hygienic, 2 = captured)\n" (with-tmp tmp))
  (run))
