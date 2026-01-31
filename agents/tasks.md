# LeanRustLisp Core Implementation Task List

Based on [agents/core_implementation.md](agents/core_implementation.md).

## Phase 0: Freeze the Design Contract (Spec-First)
- [/] **Core Calculus Spec** ([docs/spec/core_calculus.md](docs/spec/core_calculus.md)) - *Needs expansion*
- [/] **Fragment Separation Spec** ([docs/spec/kernel_definition.md](docs/spec/kernel_definition.md)) - *High-level drafted*
- [/] **Ownership + Effects Spec** ([docs/spec/ownership_model.md](docs/spec/ownership_model.md)) - *Drafted*

## Phase 1: Kernel Hardening (Make the Lean part real)

### A. Shrink the Trusted Boundary
- [x] **Remove Parsing from Kernel**
    - [x] Create `frontend` crate
    - [x] Verify `kernel` crate depends ONLY on AST, not text (Parser moved to test_support)
    - [x] Minimal Kernel API (Restricted exports)

### B. Implement Definitional Equality properly
- [x] **Robust DefEq Engine**
    - [x] Audit current `is_def_eq` (Fixed universe param check)
    - [x] Implement checks for reduction rules (beta, delta, iota, zeta)
    - [x] Transparency levels (reducible/semireducible)

### C. Inductives and Eliminators (General)
- [x] **General Inductive Support**
    - [x] Parameterized Inductives (List, custom types work)
    - [x] Positivity check (Strict positivity implemented)
    - [/] Universe level constraints for inductives (Placeholder structure)
    - [ ] Indices (W-types or direct)

### D. Totality/Termination ✅ COMPLETED
- [x] **Totality Markers**
    - [x] `Totality` enum: `Total`, `WellFounded`, `Partial`, `Axiom`, `Unsafe`
    - [x] `Definition` struct with totality tracking
    - [x] `WellFoundedInfo` for well-founded recursion specs
- [x] **Structural Recursion Checking**
    - [x] `TerminationCtx` for tracking smaller variables
    - [x] `check_termination()` with nested pattern support
    - [x] Recursor application analysis (`check_rec_app`)
    - [x] Minor premise verification (`check_minor_premise`)
    - [x] IH variable tracking through recursors
- [x] **Type Safety Enforcement**
    - [x] `contains_partial_def()` to detect partial defs in types
    - [x] `add_definition()` rejects types containing partial defs
    - [x] `PartialInType` error type
- [x] **Surface Syntax**
    - [x] `(def name type value)` - Total definition
    - [x] `(partial name type value)` - Partial definition
    - [x] `(axiom name type)` - Axiom declaration
- [x] **Well-Founded Recursion Infrastructure**
    - [x] `WellFoundedInfo` struct in ast.rs
    - [x] `WellFoundedSpec` struct in checker.rs (detailed)
    - [x] `WellFoundedCtx` for tracking accessible values
    - [x] `WellFoundedError` enum for detailed WF errors
    - [x] `check_wellfounded_termination()` with Acc verification
    - [x] `is_wellfoundedness_proof_type()` for proof type checking
    - [x] `check_wellfounded_calls()` for recursive call verification
- [x] **Mutual Recursion Analysis**
    - [x] `build_call_graph()` - builds function call graph
    - [x] `find_mutual_groups()` - identifies mutually recursive groups
    - [x] `can_reach()` - call graph reachability
    - [x] `check_mutual_termination()` - verifies compatible decreasing arguments
    - [x] `check_termination_mutual()` - termination in mutual context
    - [x] `check_mutual_recursive_calls()` - validates mutual calls
    - [x] `collect_app_spine()` - helper for application analysis
- [x] **Error Messages & Diagnostics**
    - [x] `TerminationErrorDetails` enum with detailed variants
    - [x] `NonSmallerArgument` with arg position and smaller vars info
    - [x] `NoDecreasingArgument` for missing inductive argument
    - [x] `RecursiveCallInType` for recursive calls in type position
    - [x] `MutualRecursionError` with function list
    - [x] `GeneralRecursion` for non-structural recursion
- [x] **Automatic Decreasing Argument Detection**
    - [x] `check_termination()` returns `Option<usize>` for decreasing arg
    - [x] `add_definition()` auto-sets `rec_arg` field
    - [x] `contains_recursor_usage()` to detect recursor-based recursion
- [x] **Tests** (12 termination-related tests)
    - [x] `test_totality_markers`
    - [x] `test_termination_non_recursive`
    - [x] `test_termination_with_recursor`
    - [x] `test_env_type_safety`
    - [x] `test_partial_in_type_rejected`
    - [x] `test_wellfounded_definition`
    - [x] `test_automatic_rec_arg_tracking`
    - [x] `test_termination_rejection_non_smaller_arg`
    - [x] `test_termination_rejection_no_decreasing_arg`
    - [x] `test_mutual_recursion_valid`
    - [x] `test_mutual_recursion_incompatible_args`
    - [x] `test_wellfounded_recursion_with_acc`
    - [x] `test_wellfounded_context`

### D. Totality/Termination - Future Refinements
- [x] Full verification of well-founded proofs (Acc type verification implemented)
- [x] Mutual recursion analysis across definition groups (call graph analysis implemented)
- [/] CLI integration tests for termination rejection (requires Phase 3 elaborator support for match)

## Phase 2: Make Macros Real ✅ COMPLETED
- [x] **Syntax objects with hygiene and spans**
    - [x] `Span` type with start, end, line, col
    - [x] `ScopeId` type for hygiene tracking
    - [x] `Syntax` type with kind, span, scopes fields
    - [x] Spans preserved through parsing and expansion
- [x] **Scope-based hygiene**
    - [x] `new_scope()` - generates unique scope IDs
    - [x] `substitute_rec_with_scope()` - adds macro scope during expansion
    - [x] `scopes_compatible()` - checks scope compatibility for binding
    - [x] `add_scope()` / `remove_scope()` - explicit scope manipulation
    - [x] Macro-introduced syntax gets macro scope
    - [x] Argument syntax keeps original scopes (proper hygiene)
- [x] **Staging and determinism**
    - [x] `gensym()` for fresh name generation
    - [x] Deterministic macro expansion (single-threaded, no side effects)
    - [x] Macros expand at declaration parsing time (compile-time)
- [x] **Macro debugging (`:expand`)**
    - [x] Working `:expand` REPL command
    - [x] `pretty_print()` for syntax visualization
- [x] **Tests** (5 hygiene-related tests)
    - [x] `test_hygiene_scope_creation`
    - [x] `test_hygiene_scopes_compatible`
    - [x] `test_macro_expansion_adds_scope`
    - [x] `test_macro_introduced_syntax_gets_scope`
    - [x] `test_add_remove_scope`

## Phase 3: Elaborator Upgrades
- [x] **Real declaration AST**
    - [x] `Declaration` enum with Def, Axiom, Inductive, DefMacro, Expr
    - [x] `DeclarationParser` for parsing declarations
- [/] **Bidirectional elaboration + metavariables**
    - [x] `infer()` method for type inference
    - [x] `check()` method for type checking
    - [x] Metavariable tracking (`meta_counter`, `meta_solutions`, `meta_contexts`)
    - [x] `unify()` with occurs check
    - [x] Advanced constraint solving
    - [x] Constraint postponement
- [x] **Implicit arguments** ✅ COMPLETED
- [x] **Pattern matching elaboration** ✅ COMPLETED
    - [x] `match_list` expands to recursors (works)
    - [x] `match` surface syntax exists
    - [x] Direct Match elaboration in elaborator (`elaborate_match`)
    - [x] Case branch elaboration (`elaborate_case`)
    - [x] IH (induction hypothesis) type handling
    - [x] Constructor argument binding
    - [x] Recursor application generation

## Phase 4: Ownership and Borrowing (Rust Reliability)
- [x] **Mid-level IR (LRL-MIR)**
    - [x] Create `mir` crate
    - [x] Define types (BasicBlock, Statement, Terminator)
    - [x] Implement AST -> MIR Lowering
- [x] **Ownership Analysis**
    - [x] Initialization & Move analysis (Full local tracking)
    - [x] Partial Move Safety (Conservative tracking)
    - [x] Argument Evaluation Sequencing (Prevent double moves in args)
    - [x] Drop/Destructor checking (Linear types)
    - [x] Variable Initialization Analysis (Detect uninit usage)
    - [x] Return Value Initialization Check (Prevent uninit return)
    - [x] Partial initialization handling (basic)
- [x] **Borrow Checking**
    - [x] Reference types & Borrowing rules (Basic)
    - [x] Assignment Conflict Checking (Prevent assigning to borrowed place)
    - [x] Lifetime Analysis (Prevent escaping references)
    - [x] Disjoint Field Borrowing (Split borrows)
    - [x] Drop/Destructor checking
    - [x] Mutability Checking (Prevent mutating shared refs)

## Phase 5: Effects, Partial, and Unsafe
## Phase 5: Effects, Partial, and Unsafe
- [x] Separation boundary enforcement
    - [x] Implement `check_effects` in Checker
    - [x] `def` (Total) cannot call Partial/Unsafe
    - [x] `partial` cannot call Unsafe
    - [x] `Comp` type introduction
    - [x] Tests for boundary violations

## Phase 6: Backend and Runtime
- [ ] Typed backend path
- [x] Closure conversion and data layout
- [x] Proof erasure

## Phase 7: Stdlib and Language Feel
- [ ] Kernel-proximal stdlib (`Nat`, `Bool`, `List`, `Eq`)
- [ ] Rust-grade stdlib (`Vec`, `Map`)
- [ ] Lisp-grade stdlib (Macro utils)

---

## Test Summary
- **Kernel tests**: 26 passing
- **Frontend tests**: 7 passing
- **Mir tests**: 1 passing
- **Total**: 34 passing

## Recent Changes (This Session)
1. **Phase 4: MIR Infrastructure**
   - Created `mir` crate and defined core CFG structures (`BasicBlock`, `Statement`, `Terminator`).
   - Implemented AST-to-MIR lowering logic for `Let`, `App`, and `Const`.
   - Handled De Bruijn index translation to MIR Locals.
   - Verified lowering logic with unit tests.
2. **Match Elaboration** (Phase 3 completion)
   - Implemented `elaborate_match()` in elaborator to convert match expressions to recursor applications
   - Implemented `elaborate_case()` for case branch elaboration
   - Added support for `Ind`, `Ctor`, `Rec` term kinds in elaborator
   - Fixed IH type computation for non-dependent matches
   - Fixed Pi/Let type checking to allow universe polymorphism
3. **Delta Reduction** (WHNF bug fix)
   - Added `Term::Const` unfolding to `whnf()` function
   - Definitions now properly reduce during evaluation
4. **Universe Polymorphism Fix**
   - Changed Pi/Let elaboration to infer domain type instead of checking against Sort(0)
   - Allows parameterized inductives like `List` to work correctly
5. **Prelude Updates**
   - All prelude functions now work (`add`, `not`, `and`, `or`, `if_nat`)
   - List inductive definition now elaborates correctly
6. Auto-populate `rec_arg` in `add_definition()`
7. Added `contains_recursor_usage()` for recursor detection
8. Implemented full mutual recursion analysis:
   - Call graph construction
   - Mutual group detection
   - Compatible decreasing argument verification
9. Enhanced well-founded recursion infrastructure:
   - `WellFoundedSpec` with proof verification
   - `WellFoundedCtx` for accessibility tracking
   - `WellFoundedError` for detailed errors
   - Acc type verification when present
10. Fixed `Declaration::Inductive` handling in CLI
11. Added 6 new tests for mutual recursion and well-founded verification
