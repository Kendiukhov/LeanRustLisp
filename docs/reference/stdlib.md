# Standard Library Reference

The LeanRustLisp standard library provides core types, data structures, and algorithms for building verified software.

## Architecture

```
stdlib/
├── prelude_api.lrl          # Public API contract (all backends)
├── prelude_impl_dynamic.lrl # Dynamic backend platform layer
├── prelude_impl_typed.lrl   # Typed backend platform layer
└── std/
    ├── core/                # Primitives: Bool, Nat, Int, Float
    ├── data/                # Collections: List, Option, Result, Pair
    └── control/             # Effects: Comp
```

**Important**: User code should target `prelude_api` only. Never import `prelude_impl_*` directly.

---

## Numeric Types

### Nat

Natural numbers (non-negative integers) with Peano encoding.

```lisp
(inductive copy Nat (sort 1)
  (ctor zero Nat)
  (ctor succ (pi n Nat Nat)))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `add` / `+` | `Nat → Nat → Nat` | Addition |
| `nat_mul` / `*` | `Nat → Nat → Nat` | Multiplication |
| `nat_div` / `/` | `Nat → Nat → Nat` | Floor division (div by 0 → 0) |
| `nat_pred` | `Nat → Nat` | Saturating predecessor (0 for zero) |
| `nat_sub` | `Nat → Nat → Nat` | Bounded subtraction (clamps to 0) |
| `nat_is_zero` | `Nat → Bool` | Test if zero |
| `nat_eq` | `Nat → Nat → Bool` | Equality |
| `nat_lt` | `Nat → Nat → Bool` | Less than |
| `nat_le` | `Nat → Nat → Bool` | Less or equal |
| `nat_gt` | `Nat → Nat → Bool` | Greater than |
| `nat_ge` | `Nat → Nat → Bool` | Greater or equal |

---

### Int

Signed integers represented as sign + magnitude.

```lisp
(inductive copy Int (sort 1)
  (ctor int_pos (pi n Nat Int))   ;; Positive or zero
  (ctor int_neg (pi n Nat Int)))  ;; Negative
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `int_from_nat` | `Nat → Int` | Convert Nat to positive Int |
| `int_to_nat` | `Int → Nat` | Clamp to Nat (negative → 0) |
| `int_abs` | `Int → Nat` | Absolute value |
| `int_negate` | `Int → Int` | Negate sign |
| `int_normalize` | `Int → Int` | Normalize (−0 → +0) |
| `int_add` / `+i` | `Int → Int → Int` | Addition |
| `int_sub` / `-i` | `Int → Int → Int` | Subtraction |
| `int_mul` / `*i` | `Int → Int → Int` | Multiplication |
| `int_div` / `/i` | `Int → Int → Int` | Truncating division (toward zero) |
| `-` | `Nat → Nat → Int` | Subtraction returning signed result |

---

### Float

Half-precision floating point (IEEE-754 binary16).

```lisp
(inductive copy Float (sort 1)
  (ctor float16 (pi bits Nat Float)))  ;; 16-bit payload in Nat
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `float_from_bits` | `Nat → Float` | Create from IEEE-754 bits |
| `float_to_bits` | `Float → Nat` | Extract IEEE-754 bits |
| `+f` | `Float → Float → Float` | Addition |
| `-f` | `Float → Float → Float` | Subtraction |
| `*f` | `Float → Float → Float` | Multiplication |
| `/f` | `Float → Float → Float` | Division |

> **Note**: Float arithmetic is implemented as backend builtins. The bodies in std are placeholders.

---

## Boolean Type

### Bool

Boolean type with standard logical operations.

```lisp
(inductive copy Bool (sort 1)
  (ctor true Bool)
  (ctor false Bool))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `not` | `Bool → Bool` | Logical negation |
| `and` | `Bool → Bool → Bool` | Logical AND |
| `or` | `Bool → Bool → Bool` | Logical OR |
| `xor` | `Bool → Bool → Bool` | Exclusive OR |
| `implies` | `Bool → Bool → Bool` | Logical implication (a → b) |
| `bool_eq` | `Bool → Bool → Bool` | Boolean equality |
| `if_nat` | `Bool → Nat → Nat → Nat` | Conditional for Nat |
| `if_bool` | `Bool → Bool → Bool → Bool` | Conditional for Bool |

---

## Data Structures

### List

Polymorphic linked list.

```lisp
(inductive copy List (pi T (sort 1) (sort 1))
  (ctor nil (pi {T (sort 1)} (List T)))
  (ctor cons (pi {T (sort 1)} (pi h T (pi t (List T) (List T))))))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `append` | `List Nat → List Nat → List Nat` | Concatenate lists |
| `length` | `List Nat → Nat` | Compute list length |
| `map` | `(Nat → Nat) → List Nat → List Nat` | Apply function to each element |
| `foldr` | `(Nat → Nat → Nat) → Nat → List Nat → Nat` | Right fold |
| `foldl` | `(Nat → Nat → Nat) → Nat → List Nat → Nat` | Left fold |
| `reverse` | `List Nat → List Nat` | Reverse list order |
| `filter` | `(Nat → Bool) → List Nat → List Nat` | Keep matching elements |

---

### Option

Optional values for computations that may fail.

```lisp
(inductive copy Option (pi T (sort 1) (sort 1))
  (ctor none (pi {T (sort 1)} (Option T)))
  (ctor some (pi {T (sort 1)} (pi x T (Option T)))))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `option_map` | `(A → B) → Option A → Option B` | Map over Some |
| `option_and_then` | `Option A → (A → Option B) → Option B` | Monadic bind |
| `option_flat_map` | `Option A → (A → Option B) → Option B` | Alias for and_then |
| `option_unwrap_or` | `A → Option A → A` | Default value for None |
| `option_or` | `Option A → Option A → Option A` | Left-biased choice |
| `option_is_some` | `Option A → Bool` | Test for Some |
| `option_is_none` | `Option A → Bool` | Test for None |

---

### Result

Error handling with typed errors.

```lisp
(inductive copy Result (pi E (sort 1) (pi T (sort 1) (sort 1)))
  (ctor err (pi {E (sort 1)} (pi {T (sort 1)} (pi e E (Result E T)))))
  (ctor ok (pi {E (sort 1)} (pi {T (sort 1)} (pi x T (Result E T))))))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `result_map` | `(A → B) → Result E A → Result E B` | Map over Ok |
| `result_map_err` | `(E1 → E2) → Result E1 A → Result E2 A` | Map over Err |
| `result_and_then` | `Result E A → (A → Result E B) → Result E B` | Monadic bind |
| `result_unwrap_or` | `A → Result E A → A` | Default for Err |
| `result_or` | `Result E A → Result E A → Result E A` | Left-biased choice |
| `result_is_ok` | `Result E A → Bool` | Test for Ok |
| `result_is_err` | `Result E A → Bool` | Test for Err |

---

### Pair

Product types (tuples).

```lisp
(inductive copy Pair (pi A (sort 1) (pi B (sort 1) (sort 1)))
  (ctor mk_pair (pi {A (sort 1)} (pi {B (sort 1)} (pi fst A (pi snd B (Pair A B)))))))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `pair_fst` | `Pair A B → A` | First projection |
| `pair_snd` | `Pair A B → B` | Second projection |
| `pair_map` | `(Nat → Nat) → (Nat → Nat) → Pair Nat Nat → Pair Nat Nat` | Map both |
| `pair_map_fst` | `(Nat → Nat) → Pair Nat Nat → Pair Nat Nat` | Map first |
| `pair_map_snd` | `(Nat → Nat) → Pair Nat Nat → Pair Nat Nat` | Map second |

---

## Text and I/O

### Text

UTF-32 encoded string type.

```lisp
(inductive copy Text (sort 1)
  (ctor text (pi data (List Nat) Text)))
```

#### Functions

| Function | Type | Description |
|----------|------|-------------|
| `print` | `Text → Text` | Print text to stdout |
| `print_text` | `Text → Text` | Print text (typed backend) |
| `print_nat` | `Nat → Nat` | Print Nat to stdout |
| `print_bool` | `Bool → Bool` | Print Bool to stdout |
| `print_float` | `Float → Float` | Print Float to stdout |
| `read_file` | `Text → Text` | Read file contents |
| `write_file` | `Text → Text → Text` | Write contents to file |

---

## Special Types

### Borrowing Primitives

```lisp
(axiom Shared (sort 1))    ;; Shared reference mode
(axiom Mut (sort 1))       ;; Mutable reference mode
(axiom Ref (pi k (sort 1) (pi A (sort 1) (sort 1))))
(axiom borrow_shared (pi {A (sort 1)} (pi x A (Ref Shared A))))
(axiom borrow_mut (pi {A (sort 1)} (pi x A (Ref Mut A))))
```

### Container Types

| Type | Attributes | Description |
|------|------------|-------------|
| `VecDyn T` | `indexable` | Dynamic vector |
| `Slice T` | `indexable` | Borrowed slice |
| `Array T` | `indexable` | Fixed-size array |
| `RefCell T` | `interior_mutable` | Runtime-checked mutable cell |
| `Mutex T` | `concurrency_primitive` | Thread-safe lock |
| `Atomic T` | `atomic_primitive` | Atomic value |

### Logical Types

```lisp
(inductive False (sort 0))  ;; Empty type (absurdity)

(inductive Eq (pi A (sort 1) (pi a A (pi b A (sort 0))))
  (ctor refl (pi A (sort 1) (pi a A (Eq A a a)))))
```

---

## Usage Examples

### Hello World

```lisp
;; Print text to console
(print (text (cons 72 (cons 101 (cons 108 (cons 108 (cons 111 nil)))))))
```

### Basic Arithmetic

```lisp
(def two Nat (succ (succ zero)))
(def four Nat (+ two two))           ;; Using operator alias
(def product Nat (* two four))       ;; Multiplication
(def quotient Nat (/ product two))   ;; Division
```

### Signed Integer Arithmetic

```lisp
;; Create negative numbers
(def neg_five Int (int_neg (succ (succ (succ (succ (succ zero)))))))

;; Arithmetic with Int
(def sum Int (+i (int_pos two) neg_five))  ;; -3
(def diff Int (- (succ zero) two))         ;; -1 (Nat subtraction returning Int)
```

### Floating Point

```lisp
(def x Float (float16 (succ (succ zero))))  ;; Create float from bits
(def y Float (+f x x))                       ;; Add floats
(def z Float (*f x (float16 zero)))          ;; Multiply
```

### List Operations

```lisp
(def nums (List Nat) (cons (succ zero) (cons (succ (succ zero)) nil)))
(def len Nat (length nums))
(def doubled (List Nat) (map (lam #[fn] x Nat (+ x x)) nums))
```

### Option Handling

```lisp
(def maybe_val (Option Nat) (some (succ (succ zero))))
(def result Nat (option_unwrap_or Nat zero maybe_val))
```

### Result Chaining

```lisp
(def success (Result Nat Nat) (ok (succ zero)))
(def doubled (Result Nat Nat) 
  (result_map Nat Nat Nat 
    (lam #[fn] x Nat (+ x x)) 
    success))
```
