  
• Reviewed kernel, frontend, mir, and codegen (codegen is explicitly incomplete). Overall status is  
  still research prototype; several soundness, determinism, and runtime safety gaps would block  
  industrial use today.

  Prototype Smells \- Kernel

  \- kernel/src/checker.rs::check\_universe\_levels is a stub; universe constraints are not enforced so  
    inductives can be unsound; industrial alternative is full universe constraint checking with  
    explicit error reporting and tests for under- and over-universe constructors.  
  \- kernel/src/checker.rs::check\_positivity only checks a shallow shape and uses name matching; it  
    misses many negative positions and nested occurrences; industrial alternative is a strict-  
    positivity pass with polarity tracking and proper handling of parameters vs indices.  
  \- kernel/src/checker.rs::whnf and is\_def\_eq\_in\_ctx run NbE with unlimited reduction and no cache;  
    this is a defeq performance cliff and can diverge; industrial alternative is a reduction budget  
    with caching and an explicit fuel exhaustion error surfaced to diagnostics.  
  \- kernel/src/checker.rs::check\_wellfounded\_termination is not called by Env::add\_definition for  
    Totality::WellFounded, but nbe::eval still unfolds those defs as total; this can make defeq  
    unsound; industrial alternative is mandatory WF proof checking before marking a def unfoldable.  
  \- kernel/src/nbe.rs::apply\_with\_config panics on non-function application and other internal  
    mismatches; a trusted kernel should not panic on ill-typed terms; industrial alternative is to  
    return a neutral or typed error and fail gracefully.  
  \- kernel/src/checker.rs::compute\_recursor\_type and infer\_num\_params\_from\_ctors contain complex,  
    brittle de Bruijn index logic with limited tests; industrial alternative is to isolate inductive/  
    recursor construction into a dedicated module with explicit binder data structures and regression  
    tests for indexed types.

  Prototype Smells \- Frontend

  \- frontend/src/macro\_expander.rs::expand\_with\_env resolves identifiers by exact (name, scopes)  
    match, but scopes\_compatible is unused; hygiene can fail and macro-introduced identifiers may not  
    resolve; industrial alternative is scope-compatibility resolution with longest matching scope set.  
  \- frontend/src/macro\_expander.rs::substitute\_rec\_with\_scope adds macro scope to all nodes, including  
    user-supplied arguments and literals; this leaks scopes and breaks referential transparency;  
    industrial alternative is to add macro scopes only to syntax introduced by the macro, preserving  
    argument scopes.  
  \- frontend/src/elaborator.rs::solve\_meta checks free variables against the current ctx length but  
    ignores meta\_contexts; meta solutions can be ill-scoped or rejected incorrectly; industrial  
    alternative is context-aware meta substitution with explicit context pruning and zonking.  
  \- frontend/src/elaborator.rs::infer\_rec\_application infers a single universe level from the motive  
    and ignores univ\_params; universe-polymorphic recursors are incomplete; industrial alternative is  
    to compute the full level vector from the motive type and inductive parameters.  
  \- frontend/src/parser.rs has SyntaxKind::String but no string literal support, and frontend/src/  
    quote\_helper.rs/frontend/src/quasiquote\_helper.rs are orphan prototype files; industrial  
    alternative is to either wire these into the module or delete them to avoid spec drift.

  Prototype Smells \- MIR and Codegen

  \- mir/src/lower.rs::lower\_type hard-codes Ref, Mut, Shared, List, Nat, Bool by name strings; this is  
    not extensible and not tied to kernel type info; industrial alternative is a typed lowering table  
    keyed by resolved inductive/const IDs.  
  \- mir/src/lower.rs::lower\_term uses expect on de Bruijn bounds and falls back to Sort(Type 0\) when  
    inference fails; this can panic or silently mis-type MIR; industrial alternative is to propagate  
    typed lowering errors and require inference success.  
  \- cli/src/compiler.rs runs mir/src/analysis/nll.rs for top-level defs but mir/src/analysis/borrow.rs  
    for closures; this creates two inconsistent borrow semantics; industrial alternative is one NLL-  
    based checker for all bodies.  
  \- mir/src/analysis/nll.rs::BorrowCheckResult computes runtime\_checks but mir/src/codegen.rs never  
    emits them; interior mutability checks are effectively dropped; industrial alternative is MIR  
    statements for runtime checks with codegen support.  
  \- mir/src/codegen.rs uses a dynamic Value with many panic\! paths in recursors and constructors;  
    well-typed programs can still panic on runtime tag mismatches; industrial alternative is typed  
    Rust enums per inductive and a panic-free runtime path for the safe profile.  
  \- mir/src/types.rs::MirType::Adt erases indices and Place projections are untyped; borrow conflicts  
    and field accesses are approximations; industrial alternative is to track variant and field types  
    in MIR and use them in borrow/codegen.

  Industrialization Roadmap  
  Phase 1

  \- Tasks: implement strict positivity and universe checks; enforce well-founded recursion proof  
    checking; add defeq fuel plus cache; fix macro hygiene resolution; unify NLL for all bodies; emit  
    runtime checks; remove kernel panics.  
  \- Dependencies: agree on inductive/universe rules, transparency policy, and interior mutability  
    policy; stabilize MIR Place typing.  
  \- Risk: high; touches kernel, elaborator, MIR, and codegen interfaces.  
  \- Acceptance tests: kernel positivity/universe regression tests, defeq fuel exhaustion test, macro  
    hygiene capture tests, NLL borrow tests, and runtime check emission tests.

  Phase 2

  \- Tasks: defeq memoization and normalization cache; stable term hashing; deterministic macro  
    expansion and env ordering; incremental compilation and MIR caching; replace debug prints with  
    structured diagnostics.  
  \- Dependencies: Phase 1 APIs for reduction and MIR shape.  
  \- Risk: medium.  
  \- Acceptance tests: defeq microbench regression, deterministic build test (same input \-\> same  
    output), and incremental compile speed test.

  Phase 3

  \- Tasks: span-rich diagnostics across kernel/MIR, multi-file module system, artifact cache, basic  
    LSP integration, and doc generation hooks.  
  \- Dependencies: stable AST/span mapping and error categories.  
  \- Risk: medium to low.  
  \- Acceptance tests: multi-file build integration tests, LSP smoke tests, and artifact cache  
    correctness tests.

  Hard Requirements Checklist (v0.1 core)  
  Kernel/Core

  \- Deterministic compilation (same input \-\> same output) \- Status: partial; HashMap usage is mostly  
    sorted but defeq fuel is env-dependent and debug prints leak nondeterminism.  
  \- Clear kernel boundary (TCB minimal) \- Status: partial; driver re-checks, but kernel panics are  
    still possible in NbE.  
  \- Definitional equality principled (NbE or equivalent) \- Status: partial; NbE exists but lacks  
    guardrails, caching, and fuel errors.  
  \- Inductives/eliminators generality (no Nat/Bool/List special cases in semantics) \- Status: partial;  
    kernel is mostly generic, but MIR and codegen special-case heavily.  
  \- Termination and well-founded recursion soundness \- Status: needs work; WellFounded is not verified  
    before unfolding.

  Borrowing and Runtime

  \- NLL-ready MIR with CFG, regions, constraints, diagnostics \- Status: partial; CFG exists and NLL  
    prototype works but spans and full constraint coverage are missing.  
  \- Borrow checker output integrated into codegen \- Status: missing; runtime checks are computed but  
    unused.  
  \- Panic-free safe subset definition and enforcement points \- Status: partial; PanicFreeLinter exists  
    but codegen still panics.  
  \- Interior mutability policy explicit and enforced (RefCell/Mutex/Atomic) \- Status: partial; types  
    exist but naming/documentation and runtime hooks are missing.  
  \- Ownership/linearity semantics preserved across kernel \-\> MIR \- Status: partial; kernel ownership  
    checker is unused and MIR analysis is independent.

  Determinism and Tooling

  \- Stable error categories and spans \- Status: partial; frontend spans exist but kernel errors lack  
    span mapping.  
  \- Transparency defaults plus escape hatches plus defeq performance guardrails \- Status: partial;  
    opaque exists but there are no defeq metrics or budget handling.  
  \- Reproducible builds and artifact caching \- Status: missing; rustc is invoked without deterministic  
    flags or compiler cache.  
  \- Incremental compilation \- Status: missing.  
  \- Spec-level tests and fuzzing \- Status: partial; unit tests exist, no fuzz or spec-invariant suite.

  Concrete Proposed Changes (top 5 issues)

  1\. Kernel reduction and defeq guardrails  
     Change kernel/src/nbe.rs and kernel/src/checker.rs to thread a DefEqConfig with fuel and cache,  
     and return a typed error on exhaustion. Add a small cache keyed by (term hash, transparency,  
     level) to avoid repeated unfolding. Example sketch:

  pub struct DefEqConfig { pub transparency: Transparency, pub fuel: usize, pub cache:  
  FxHashMap\<HashKey, Value\> }

  pub fn whnf\_with(env: \&Env, ctx: \&Context, t: Rc\<Term\>, cfg: \&mut DefEqConfig) \-\> Result\<Rc\<Term\>,  
  TypeError\> { /\* ... \*/ }

  Update check and infer to use whnf\_with and surface TypeError::DefEqFuelExhausted. Add tests in  
  kernel/tests for fuel exhaustion and caching correctness.

  2\. Inductive soundness plus well-founded recursion enforcement  
     Split inductive checks into kernel/src/inductive.rs and replace check\_positivity and  
     check\_universe\_levels with strict versions; update check\_inductive\_soundness to call them. Extend  
     Env::add\_definition to require a verified WellFoundedInfo before treating Totality::WellFounded  
     as unfoldable, and return a new error when missing or invalid. Add tests for negative  
     occurrences, universe mismatches, and WF proof enforcement.  
  3\. Macro hygiene resolution  
     Refactor frontend/src/macro\_expander.rs so env is keyed by name and supports scope compatibility;  
     prefer the longest compatible scope set deterministically. Preserve user scopes for macro  
     arguments and only add the macro scope to introduced syntax. Example lookup:

  fn resolve(name: \&str, ref\_scopes: &\[ScopeId\]) \-\> Option\<String\> {  
    env.get(name)  
       .and\_then(|defs| defs.iter()  
         .filter(|(def\_scopes, \_)| Expander::scopes\_compatible(ref\_scopes, def\_scopes))  
         .max\_by\_key(|(def\_scopes, \_)| def\_scopes.len())  
         .map(|(\_, v)| v.clone()))  
  }

  Add hygiene tests covering capture avoidance, argument scope preservation, and nested macros.

  4\. Elaborator meta scoping and unification  
     Fix frontend/src/elaborator.rs so meta solutions are context-aware: store a full MetaCtx with  
     binder types, and solve metas by abstracting over that context. Implement zonk (recursive meta  
     resolution) and use it before kernel re-checking. Add tests for implicit args and metas that  
     require context pruning.  
  5\. MIR borrow integration and codegen runtime safety  
     Use mir/src/analysis/nll.rs for all bodies in cli/src/compiler.rs and cli/src/driver.rs,  
     deprecating mir/src/analysis/borrow.rs or making it a thin wrapper. Add a MIR statement for  
     runtime checks (e.g., Statement::RuntimeCheck(RuntimeCheck)) and teach mir/src/codegen.rs to emit  
     them. Start eliminating panics for well-typed code by generating typed enums for inductives in  
     codegen or by returning Result\<Value, RuntimeError\> for dynamic checks. Add tests that assert  
     runtime checks are emitted for IMKind::RefCell and that a well-typed program does not panic.

  Non-goals / Tradeoffs

  \- Do not build a full dependent pattern compiler in v0.1; keep match elaboration as recursor  
    lowering.  
  \- Do not add full universe polymorphism inference yet; require explicit levels and focus on  
    soundness.  
  \- Do not pursue heavy optimization passes until defeq, inductives, and borrow checks are stable.  
  \- Do not attempt full LSP or package manager in v0.1; focus on deterministic diagnostics and core  
    CLI.

  Issue List  
  Kernel

  \- blocker kernel: Implement strict positivity checking \- Acceptance: reject negative occurrences and  
    accept Nat/List/Vec cases with tests.  
  \- blocker kernel: Implement universe level constraints for inductives \- Acceptance: constructors  
    with too-large fields are rejected with UniverseLevelTooSmall.  
  \- high kernel: Add defeq fuel plus cache and surface fuel exhaustion \- Acceptance: defeq returns a  
    typed error when fuel is exhausted.  
  \- high kernel: Enforce well-founded recursion proof checking \- Acceptance: WellFounded defs require  
    Acc proof or fail to add.  
  \- med kernel: Remove panics from NbE apply path \- Acceptance: kernel never panics on ill-typed  
    terms; returns typed errors.

  Frontend

  \- high frontend: Fix macro hygiene resolution using scope compatibility \- Acceptance: macro-  
    introduced identifiers do not capture user vars in tests.  
  \- high frontend: Context-aware meta unification and zonking \- Acceptance: implicit args and metas  
    solve with correct scoping in tests.  
  \- med frontend: Implement quote/quasiquote as syntax objects or remove orphan helpers \- Acceptance:  
    no dead files; quote semantics are documented and tested.  
  \- med frontend: Support string literals in parser and surface AST \- Acceptance: parser recognizes  
    strings and round-trips spans.  
  \- low frontend: Replace debug println\! with diagnostics \- Acceptance: no debug prints in normal  
    compilation.

  MIR and Codegen

  \- high mir: Unify borrow checking to NLL for all bodies \- Acceptance: closures use NLL and borrow.rs  
    is removed or wrapped.  
  \- high mir: Emit runtime checks from BorrowCheckResult \- Acceptance: refcell/mutex checks show up in  
    generated code.  
  \- med mir: Replace name-based Ref/List lowering with typed mapping \- Acceptance: lowering uses  
    resolved inductives and prelude map.  
  \- med mir: Remove fallback typing in lowering \- Acceptance: lowering fails loudly on type inference  
    errors.  
  \- blocker codegen: Eliminate panics for well-typed programs \- Acceptance: codegen uses typed enums  
    or Result and passes panic-free tests.

  Tooling and Tests

  \- med tooling: Determinism test harness (same input \-\> same output) \- Acceptance: CI test compares  
    hashes across two runs.  
  \- med tooling: Defeq microbench and regression budget \- Acceptance: defeq bench tracked and guarded  
    in CI.  
  \- med tests: Spec-level inductive and eliminator suite \- Acceptance: positive and negative cases for  
    Nat/Vec/Eq.  
  \- low tooling: Incremental compilation cache scaffold \- Acceptance: cache hits skip re-elaboration  
    for unchanged files.  
  \- low tests: Fuzz tests for parser and elaborator \- Acceptance: fuzz runs for N minutes with no  
    crashes.  
