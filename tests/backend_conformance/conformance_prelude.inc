(inductive copy Nat (sort 1)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))

(inductive copy Bool (sort 1)
  (ctor true Bool)
  (ctor false Bool))

;; Standalone compile sentinel so this prelude asset is also a valid program.
(def conformance_probe Nat zero)
