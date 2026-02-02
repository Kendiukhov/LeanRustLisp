    fn quote_syntax(&self, syntax: &Syntax, span: Span) -> SurfaceTerm {
        match &syntax.kind {
            SyntaxKind::List(list) => {
                // (cons <head> (cons ... nil))
                let nil_tm = mk_term(SurfaceTermKind::Ctor("List".to_string(), 0), span); // nil is ctor 0
                let cons_ctor = mk_term(SurfaceTermKind::Ctor("List".to_string(), 1), span); // cons is ctor 1
                // We assume List is: inductive List (A : Type) { nil : List A, cons : A -> List A -> List A }
                // Wait, if it's polymorphic, we need to provide A?
                // `quote` usually produces an untyped list or a specific type?
                // In Lisp, `(1 2)` is just data.
                // In LRL, `[1, 2]` is likely `List Nat`. `["a"]` is `List String`.
                // `quote` on mixed types `(1 "a")` might fail or require `List Any`.
                // For now, let's assume we are quoting into a `List Nat` if all ints, or just assume the user handles types?
                // actually `quote` usually produces `Syntax` object in macro systems.
                // If I want `(quote (1 2))` to be `List Nat`, I have to infer it.
                // Given the constraints, let's make `quote` produce `Syntax` objects if we had a `Syntax` type in Kernel.
                // But we don't.
                // If the user expects `(def x (quote (1 2)))`, and `x` is `List Nat`, then `quote` must produce `List Nat`.
                // If `(quote x)` is just `x`...
                // The task description says: "Syntax objects... data: datum + span + scopes".
                // If `quote` produces `Syntax`, then we need a runtime representation of `Syntax`.
                // Since we don't have that yet, let's implement `quote` as:
                // If it's a list, make it a List term (assuming homogeneous).
                // If it's an int, make it a Nat.
                // If it's a symbol, make it a String? Or a proper Symbol type?
                // Let's settle on: `quote` desugars literals to their values.
                // List -> `List` constructors.
                // Int -> `Nat`. 
                // Symbol -> `String` (for now).
                
                let mut term = nil_tm;
                for item in list.iter().rev() {
                    let head = self.quote_syntax(item, span);
                    // App(App(cons, head), tail) ?? 
                    // Cons : A -> List A -> List A.
                    // We need implicit args?
                    // SurfaceTerm `App` allows implicits.
                    // If we rely on elaborator to infer A, we can just do `cons head tail`.
                    let app1 = mk_term(SurfaceTermKind::App(Box::new(cons_ctor.clone()), Box::new(head), true), span);
                    term = mk_term(SurfaceTermKind::App(Box::new(app1), Box::new(term), true), span);
                }
                term
            },
            SyntaxKind::Int(n) => {
                // Return Nat literal? We don't have Nat literal in SurfaceTermKind yet? 
                // We do have `Rec` / `Zero` / `Succ`.
                // Let's produce the Nat term chain.
                let mut t = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 0), span); // Zero
                let succ = mk_term(SurfaceTermKind::Ctor("Nat".to_string(), 1), span); // Succ
                for _ in 0..*n {
                    t = mk_term(SurfaceTermKind::App(Box::new(succ.clone()), Box::new(t), true), span);
                }
                t
            },
            SyntaxKind::String(s) => {
                // Do we have String? No. 
                // Treat as error or maybe dummy?
                mk_term(SurfaceTermKind::Var("StringNotImplemented".to_string()), span)
            },
            SyntaxKind::Symbol(s) => {
                // Quoted symbol -> String?
                // Or maybe we treat it as a variable if we are building code?
                // `(quote x)` -> `x` (symbol)
                // If we don't have a Symbol type, maybe String "x"?
                 mk_term(SurfaceTermKind::Var(format!("Quote_Symbol_{}", s)), span) // Placeholder
            },
             _ => mk_term(SurfaceTermKind::Hole, span),
        }
    }
