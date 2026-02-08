# Getting Started

## Prerequisites

To build LeanRustLisp (LRL), you need the standard Rust toolchain installed:
1. `rustc`
2. `cargo`

If you don't have these, install them via [rustup.rs](https://rustup.rs).

## Building from Source

Clone the repository and build the workspace:

```bash
git clone https://github.com/leanrustlisp/leanrustlisp
cd leanrustlisp
cargo build
```

The compiled binaries will be in `target/debug`.

## Running the REPL

The easiest way to explore LRL is the Read-Eval-Print Loop (REPL).

```bash
cargo run -p cli
```

You should see a prompt:
```
LRL>
```

Try typing a simple expression:
```lisp
LRL> (add 1 2)
3 : Int
// Result evaluation and type
```

## Running a File

To interpret an LRL file directly:

```bash
cargo run -p cli -- path/to/file.lrl
```

For example, try running one of the tests:
```bash
cargo run -p cli -- tests/simple_test.lrl
```

---

## Your First Program: Hello World

Let's write and understand a complete Hello World program in LRL.

### Step 1: Create the File

Create a new file called `hello.lrl`:

```lisp
;; hello.lrl - Your first LRL program

(def greeting Text
  (text (cons 72 (cons 101 (cons 108 (cons 108 (cons 111 (cons 32 
    (cons 87 (cons 111 (cons 114 (cons 108 (cons 100 (cons 33 
    nil))))))))))))))

(print greeting)
```

### Step 2: Run It

```bash
cargo run -p cli -- compile hello.lrl
./build/output
```

You should see:
```
Hello World!
```

### Step 3: Understanding the Code

Let's break down each element:

#### Comments

```lisp
;; hello.lrl - Your first LRL program
```

Lines starting with `;;` are comments. They're ignored by the compiler.

#### Defining a Value

```lisp
(def greeting Text ...)
```

- **`def`** — Introduces a new definition
- **`greeting`** — The name we're binding
- **`Text`** — The type of the value (a text string)
- **`...`** — The value itself

In LRL, every definition has an explicit type. This enables the compiler to verify your program is well-formed.

#### Constructing Text

```lisp
(text (cons 72 (cons 101 ...)))
```

- **`Text`** is LRL's string type, defined as a wrapper around a list of Unicode code points
- **`text`** is the constructor that creates a `Text` value from a `List Nat`
- Each number is a Unicode code point:
  - `72` = 'H', `101` = 'e', `108` = 'l', `111` = 'o', `32` = ' ', etc.

#### Building Lists

```lisp
(cons 72 (cons 101 ... nil))
```

- **`nil`** — The empty list
- **`cons h t`** — Prepends element `h` to list `t`

So `(cons 72 (cons 101 nil))` creates the list `[72, 101]`.

#### Printing Output

```lisp
(print greeting)
```

- **`print`** — A built-in function that outputs `Text` to the console
- When compiled, this generates actual I/O code; in the interpreter, it's a pure identity function

### A Simpler Version (Using Nat)

If you just want to see output without dealing with strings:

```lisp
;; simple.lrl - Print a number

(def answer Nat (succ (succ (succ zero))))  ;; 3
(print_nat answer)
```

Run it:
```bash
cargo run -p cli -- compile simple.lrl && ./build/output
```

Output:
```
3
```

#### Understanding Nat

- **`Nat`** — Natural numbers (0, 1, 2, ...)
- **`zero`** — The number 0
- **`succ n`** — The successor of `n` (i.e., `n + 1`)
- So `(succ (succ (succ zero)))` = `succ(succ(1))` = `succ(2)` = `3`

### Why S-Expressions?

You might wonder why LRL uses parentheses everywhere. This is called **S-expression syntax** (from Lisp). The benefits:

1. **Homoiconicity** — Code is data, making macros natural
2. **Unambiguous parsing** — No precedence rules to remember
3. **Easy to extend** — Adding new syntax forms is trivial

Once you get used to it, `(add 1 2)` reads just as naturally as `1 + 2`.

---

## Compiling to Binary

To compile an LRL program to a standalone executable:

```bash
cargo run -p cli -- compile path/to/file.lrl -o my_program
./my_program
```

## Debugging and inspection

LRL provides several flags to help you understand what the compiler is doing.

### Macro Expansion
To see how your macros expand, use specific flags. Note that you must provide a file argument.

- `--expand-1`: Expands top-level macros one step.
- `--expand-full`: Fully expands all macros.
- `--trace-expand`: Shows the expansion process step-by-step.

```bash
cargo run -p cli -- --expand-1 path/to/file.lrl
```

### Trace Macros
To see macro expansion traces while running or compiling:
```bash
cargo run -p cli -- --trace-macros path/to/file.lrl
```

### Definitional Equality Fuel
If you hit recursion limits during type checking, you can increase the "fuel" for the definitional equality checker:
```bash
cargo run -p cli -- --defeq-fuel 1000000 path/to/file.lrl
```
