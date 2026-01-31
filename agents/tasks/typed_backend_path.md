# Typed Backend Path

---

## **North-star goals (what “typed backend path” must eventually mean)**

1. **Well-typed LRL programs never panic** due to backend tag checks (no more Expected Func, etc.), except inside explicit unsafe/FFI territory.  
2. Generated code uses **typed Rust structs/enums** for LRL inductives and uses typed Rust functions/closures where possible.  
3. Proofs (Prop) and proof-only arguments are **erased**.  
4. Dependent types are handled via **lowering**:  
   * compile-time indices erase,  
   * runtime indices become runtime fields \+ constructors enforce invariants (or checks at boundaries),  
   * never attempt “Rust expresses arbitrary dependent types.”  
5. The typed backend is **deterministic, reproducible, and testable** (golden tests \+ snapshot tests).

---

## **Precondition gate (must be true before migration starts)**

If these are not true, the typed backend work will thrash.

Gate A: semantics stability

* Kernel boundary is explicit.  
* Definitional equality is principled (NbE task underway/complete).  
* Inductives \+ recursors are correct and general.

Gate B: compiler pipeline stability

* Surface → macros → elaboration → core is stable enough to write golden tests.  
* There is a place to insert MIR lowering and (later) borrow checking (Option A).

Gate C: test harness exists

* Golden tests: .lrl program → expected stdout/type/normal form.  
* Negative tests: expected failures with stable error categories.

If gates A–C aren’t met, have the **Production-Grade Engineer** create a “readiness checklist” and block migration until it’s green.

---

## **Migration plan overview (incremental pipeline)**

You will run both backends in parallel for a while:

* **Backend D (dynamic)**: current Value enum runtime, always available.  
* **Backend T (typed)**: new typed path for a subset of programs, gradually expanding.

A selector chooses per-program or per-definition which backend to use:

* \--backend dynamic  
* \--backend typed  
* \--backend auto (typed where supported, otherwise dynamic)

The typed backend is initially conservative: it refuses cases it can’t compile safely, and falls back to dynamic.

We have borrow check already done, so there are two risks, but both are manageable:
	1.	You might accidentally design MIR around the dynamic backend.
If MIR uses “everything is Value” as its type, you’ll have to refactor MIR typing later.
Fix: make MIR typed from the start (or at least capable of carrying type info), even if dynamic backend ignores it.
	2.	You might encode “runtime borrow checks” patterns.
If you leaned on Rc<RefCell<_>>-like ideas in the backend scaffolding, you’ll later want to remove those to meet “well-typed programs don’t panic.”
Fix: treat interior mutability as explicit and carefully bounded. The borrow checker should make safe code not require runtime borrow panics.

So what’s the best order given your situation?

If borrow checking is already far along, do this:
	1.	Finalize MIR as the contract boundary

	•	Core → MIR lowering is stable.
	•	MIR carries enough type information to support typed codegen.
	•	Borrow checker runs on MIR and outputs either (a) annotated MIR or (b) “OK”.

	2.	Start typed backend from MIR, not from core terms

	•	Implement typed Rust emission for:
	•	locals with concrete types,
	•	typed ADTs for inductives,
	•	typed function signatures.
	•	Keep a fallback “dynamic Value backend” for MIR instructions you can’t type yet.

A concrete migration strategy that avoids rewrites

Phase T1 (quick win): typed data + typed locals
	•	Even if some operations still call dynamic helpers, make data representations typed:
	•	inductives → Rust enums/structs
	•	Nat/Bool → native Rust types
	•	MIR variables have Rust types.

Phase T2: eliminate dynamic Value from function boundaries
	•	Functions become typed Rust functions/closures.
	•	Calls become normal calls.
	•	Remaining dynamic operations are isolated behind explicit adapters (and are treated as “unsupported for typed backend” until handled).

Phase T3: remove “panic for well-typed programs”
	•	Any remaining dynamic checks are either:
	•	proven impossible by earlier typing/borrow checking, or
	•	turned into compile-time rejection or fallback.

---

## **Phase 0 — Define the runtime boundary & typed subset (design-only, but blocking)**

**Deliverables**

1. A document: docs/spec/codegen/runtime-repr.md with:  
   * what gets erased (Prop, proofs),  
   * which LRL core types map to Rust types,  
   * which features are “typed backend supported” in v0 and which are “fallback to dynamic.”  
2. Define a typed-backend MVP subset:  
* Supported in Typed MVP:  
  * closed terms (no free vars),  
  * inductives without parameters at first (Nat/Bool and arbitrary user inductives),  
  * functions without dependent indices in runtime (proof-only dependence ok),  
  * match/recursor compilation for those inductives.  
* Deferred:  
  * polymorphic inductives (List A),  
  * higher universes in runtime,  
  * runtime-dependent indices (Vec A n with dynamic n),  
  * effects/IO.

**Acceptance**

* A written, unambiguous spec for what Typed MVP can and cannot compile.

**Agent**

* Codegen Engineer \+ Kernel Guardian (for erasure correctness), reviewed by Production-Grade Engineer.

---

## **Phase 1 — Typed representations for non-parameterized inductives (huge ROI)**

### **Goal**

Stop representing basic data as Value; generate real Rust enums/structs for inductives.

### **Implementation tasks**

1. **Generate Rust types for inductives**  
   For each InductiveDecl (without parameters for this phase):  
* Emit:

enum Nat { Zero, Succ(Box\<Nat\>) }   
// or optimized Nat(u64) if you allow builtin lowering, but keep that as optional.

* and similarly for any user inductive:

enum MyInd { C0, C1(T1), C2(T1, T2), ... }

2. **Typed term compilation**  
   Compile core terms to typed Rust expressions:  
* Ctor becomes the constructor variant  
* Var becomes a Rust variable of the right Rust type  
* Lam becomes a Rust closure/function with typed argument  
* App becomes direct call  
* Let becomes Rust let  
* Match/Rec becomes Rust match  
3. **Remove runtime tag panics in this subset**  
   No dynamic Value pattern matches. If the program typechecks and is in supported subset, the generated Rust must not contain “Expected Func” panics.

### **Tests**

* Golden tests: Nat programs (pred, add, fold) compile via typed backend and print expected values.  
* User-defined inductive programs compile and run typed backend.

### **Acceptance**

* Typed backend compiles at least: Nat, Bool, and one user-defined inductive with multiple constructors and fields.  
* Generated Rust contains zero “tag check” panics for those programs.

**Agents**

* Codegen Engineer implements.  
* Tester adds golden tests.  
* Red Teamer tries to break “well-typed → no panic.”

---

## **Phase 2 — Dual-backend dispatcher \+ fallback logic (industrialization)**

### **Goal**

Make typed backend safe to use without blocking features.

### **Implementation tasks**

1. Add a compilation mode:  
* \--backend typed errors if unsupported constructs appear.  
* \--backend auto falls back to dynamic per-definition or per-program.  
2. Define “typed eligibility check”  
   Implement a pass that decides if a term/decl is in the typed subset:  
* no unsupported core terms,  
* no unsupported types,  
* no effects/IO (yet),  
* no polymorphism (yet).  
3. Structured error reporting  
   If typed backend rejects a program, it should explain *which construct* caused fallback (with span).

### **Tests**

* A test that typed backend refuses a polymorphic List example (for now), but auto backend compiles it dynamically.

### **Acceptance**

* Users can run \--backend auto and always get a runnable binary, with a clear warning when it falls back.

**Agents**

* Production-Grade Engineer defines the rejection UX requirements.  
* Codegen Engineer implements.  
* Tester adds “fallback reason” tests.

---

## **Phase 3 — Polymorphism strategy: generate Rust generics first (avoid reinventing monomorphization)**

The key recommendation: since you target Rust, prefer emitting Rust generics and let Rust monomorphize. Only add explicit LRL monomorphization later if necessary for performance or linking.

### **Goal**

Support parametric inductives and functions: List\<A\>, Option\<A\>, etc.

### **Implementation tasks**

1. Represent type parameters in Rust output  
* LRL List with parameter A : Type → Rust:

enum List\<A\> { Nil, Cons(A, Box\<List\<A\>\>) }

2. Compile polymorphic functions to Rust generics  
* LRL map : (A \-\> B) \-\> List A \-\> List B → Rust:

fn map\<A, B\>(f: impl Fn(A)-\>B, xs: List\<A\>) \-\> List\<B\> { ... }

3. Ensure type translation exists  
   Implement lrl\_type\_to\_rust\_type:  
* Nat \-\> u64 (or Nat enum if you keep it structural)  
* Bool \-\> bool  
* List A \-\> List\<rust(A)\>  
* Pi(A,B) \-\> impl Fn(...) \-\> ... or fn pointers where possible

### **Tests**

* List Nat and List Bool examples compile typed backend and run.  
* map, fold, length exist and work.

### **Acceptance**

* No dynamic Value required for polymorphic inductives and non-dependent polymorphic functions.

**Agents**

* Codegen Engineer implements.  
* Tester adds integration tests.  
* Production-Grade Engineer checks maintainability (avoid code explosion).

---

## **Phase 4 — Erasure becomes real: separate compile-time-only from runtime**

This is where you stop “carrying types into runtime by accident.”

### **Goal**

Implement a structured erasure pass used by typed backend:

* remove all Prop terms  
* remove proof arguments  
* prevent computation from depending on proofs

### **Implementation tasks**

1. Mark which terms/types are runtime-relevant  
* Prop and proof terms erased.  
* Terms whose only purpose is typing (Sort, Pi) erased from runtime.  
2. Enforce elimination restrictions (if not already)  
   If a program tries to branch on a Prop, typed backend rejects (or kernel forbids earlier).  
3. Update codegen to ignore erased artifacts  
   Output should be pure Rust code with only runtime constructs.

### **Tests**

* A program that includes proofs typechecks and runs; proofs do not appear in generated Rust.  
* A program that tries to compute based on proof fails (expected error).

### **Acceptance**

* Proof-heavy code generates runtime code that contains no proof objects and no proof-driven branching.

**Agents**

* Kernel Guardian defines rules; Production-Grade Engineer ensures they are enforceable.  
* Codegen Engineer implements erasure.  
* Tester writes tests.

---

## **Phase 5 — Dependent types lowering (compile-time indices vs runtime indices)**

This is the big conceptual one. The right plan is not “Rust expresses dependent types.” It’s “LRL lowers dependent types into representations.”

### **Goal**

Support a useful subset of dependent types in typed backend via lowering patterns.

### **Design decision points (must be documented)**

1. **Static index** known at compile time:  
* Vec A 3 → Rust \[A; 3\] (optional) or a Vec3\<A\> wrapper.  
2. **Dynamic index** runtime:  
* Vec A n where n not known → Rust:

struct VecDyn\<A\> { len: usize, data: Box\<\[A\]\> }

* plus invariants checked at constructors.  
3. Existentials for mutable resizing:  
* Σ n, Vec A n → runtime struct with len field.

### **Implementation tasks**

* Extend type translation to support selected indexed types.  
* Extend codegen to emit constructors that ensure invariants.  
* Keep borrow checker separate (MIR), so typed backend uses safe Rust ownership where possible.

### **Tests**

* head : Vec A (n+1) \-\> A compiles with static guarantee in typed subset (maybe only for static n first).  
* VecDyn use-case compiles and has runtime checks at boundaries.

### **Acceptance**

* Dependent-indexed programming works in at least one common pattern with typed backend.

**Agents**

* Kernel Guardian \+ Borrow Architect define which invariants are enforced where.  
* Codegen Engineer implements lowering.  
* Tester adds examples.

---

## **Phase 6 — Effects/IO mapping to typed Rust**

### **Goal**

Map your effect system (Comp ε A or similar) into idiomatic Rust.

Two feasible strategies:

* Comp as explicit context-passing \+ Result (synchronous)  
* Comp as async (later)

Implementation tasks:

* Decide effect representation.  
* Compile pure code to pure Rust.  
* Compile IO computations to functions taking a World/capability token or returning Result.

Acceptance:

* A typed-backend program with basic IO works without resorting to Value.

---

## **Phase 7 — Replace dynamic backend as default (optional endgame)**

Once typed backend covers most of the language, keep dynamic backend as:

* REPL mode / scripting mode  
* fallback for experimental features  
* debugging mode

But for “real programs,” typed backend becomes default.

---

# **Agent allocation & execution order for this migration program**

1. Kernel Guardian (ensures defeq/Prop/erasure restrictions are real)  
2. Production-Grade Engineer (stops prototype shortcuts from infecting backend)  
3. Codegen Engineer (Phase 1–3 implementation)  
4. Tester (golden tests \+ CI gates after each phase)  
5. Red Teamer (break well-typed → no panic guarantee; stress type translation)  
6. Borrow Architect (coordinate with Phase 5 and effectful runtime/FFI; MIR integration)

---

# **Recommended “stop conditions” (when to pause typed backend work)**

Pause typed backend work if:

* Kernel semantics are still changing weekly (defeq, inductives).  
* Macro expansion is nondeterministic (makes codegen tests unreliable).  
* No stable module/import/package boundary exists (typed codegen needs consistent naming and identity).

---

# **Quick list of concrete milestones (agent-friendly)**

Milestone M1 (1–2 weeks scale):

* Typed Nat/Bool \+ one user inductive.  
* No Value for these.  
* Golden tests pass.

Milestone M2:

* Dual backend selection \+ auto fallback.  
* Clear rejection reasons.

Milestone M3:

* Generic List\<A\> typed backend works using Rust generics.  
* map/fold examples.

Milestone M4:

* Proof erasure implemented \+ enforced.  
* Proofs absent from generated Rust.

Milestone M5:

* One dependent-index lowering pattern works (static or VecDyn).

This is realistic, incremental, and agent-executable. The crucial idea is: treat typed backend as a **series of expanding “supported subsets”** with an automatic safe fallback, not a rewrite.

