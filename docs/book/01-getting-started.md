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

(def entry Text
  (print "Hello, World!"))
```

The program defines a `main` entry point that prints a greeting.

### Step 2: Run It

```bash
cargo run -p cli -- compile hello.lrl
./build/output
```

You should see:
```
Hello, World!
```

### Step 3: Understanding the Code

Let's break down each element:

#### Comments

```lisp
;; hello.lrl - Your first LRL program
```

Lines starting with `;;` are comments. They're ignored by the compiler.

#### String Literals

```lisp
"Hello, World!"
```

Text enclosed in double quotes `"..."` is a **string literal**. LRL automatically converts this into a `Text` value.

#### The Program Structure

```lisp
(def entry Text
  (print "Hello, World!"))
```

- **`def`** — Introduces a new definition
- **`entry`** — The name of the definition (the last expression is evaluated)
- **`Text`** — The return type (print returns the text it prints)
- **`(print ...)`** — The body of the definition
- **`print`** — A built-in function that outputs `Text` to the console

### A More Interesting Example

Let's create a program with multiple definitions:

```lisp
;; greet.lrl - A greeting program

(def name Text "LRL User")

(def entry Text
  (print name))
```

Run it:
```bash
cargo run -p cli -- compile greet.lrl && ./build/output
```

Output:
```
LRL User
```

#### Defining Values

```lisp
(def name Text "LRL User")
```

- **`def`** — Introduces a definition
- **`name`** — The identifier
- **`Text`** — The type (required)
- **`"LRL User"`** — The value

### Printing Numbers

You can also print numbers directly:

```lisp
;; numbers.lrl - Print some numbers

(def answer Nat (+ 2 3))
(print_nat answer)
```

Output:
```
5
```

#### Understanding Nat

- **`Nat`** — Natural numbers (0, 1, 2, ...)
- **`+`** — Addition operator (prefix notation)
- **`print_nat`** — Prints a natural number

LRL also supports signed integers (`Int`) and floating-point numbers (`Float`):

```lisp
(def x Int (- 3 5))       ;; -2 (signed subtraction)
(def y Float (+f 1.5 2.5)) ;; 4.0 (float addition)
```

### Why S-Expressions?

You might wonder why LRL uses parentheses everywhere. This is called **S-expression syntax** (from Lisp). The benefits:

1. **Homoiconicity** — Code is data, making macros natural
2. **Unambiguous parsing** — No precedence rules to remember
3. **Easy to extend** — Adding new syntax forms is trivial

Once you get used to it, `(+ 1 2)` reads just as naturally as `1 + 2`.

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
