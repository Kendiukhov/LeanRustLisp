use std::collections::HashMap;
use kernel::ast::{Term, Level, InductiveDecl};
use std::rc::Rc;
use std::fmt::Write;
use anyhow::{Result, anyhow};

pub struct Codegen {
    output: String,
    indent_level: usize,
    // Stack of variable names corresponding to De Bruijn indices.
    // Index 0 is the last element.
    vars: Vec<String>, 
    var_counter: usize,
    inductives: HashMap<String, InductiveDecl>,
}

impl Codegen {
    pub fn new(inductives: HashMap<String, InductiveDecl>) -> Self {
        Codegen {
            output: String::new(),
            indent_level: 0,
            vars: Vec::new(),
            var_counter: 0,
            inductives,
        }
    }

    pub fn get_output(&self) -> &str {
        &self.output
    }

    fn fresh_var(&mut self) -> String {
        let name = format!("x_{}", self.var_counter);
        self.var_counter += 1;
        name
    }

    fn push_var(&mut self, name: String) {
        self.vars.push(name);
    }

    fn pop_var(&mut self) {
        self.vars.pop();
    }

    fn get_var(&self, idx: usize) -> Option<String> {
        if idx < self.vars.len() {
            Some(self.vars[self.vars.len() - 1 - idx].clone())
        } else {
            None
        }
    }

    pub fn emit(&mut self, term: &Term) -> Result<()> {
        match term {
            Term::Sort(l) => {
                // Types are erased to Unit
                write!(self.output, "Value::Unit")?;
            }
            Term::Var(idx) => {
                if let Some(name) = self.get_var(*idx) {
                    write!(self.output, "{}.clone()", name)?;
                } else {
                    return Err(anyhow!("Unbound variable index: {}", idx));
                }
            }
            Term::Lam(_ty, body) => {
                // Value::Func(Rc::new(move |x| { body }))
                // We must clone the environment for the move closure
                write!(self.output, "{{ ")?;
                for var in &self.vars {
                     write!(self.output, "let {} = {}.clone(); ", var, var)?;
                }
                
                let var_name = self.fresh_var();
                write!(self.output, "Value::Func(Rc::new(move |{}: Value| {{ ", var_name)?;
                
                self.push_var(var_name);
                self.emit(body)?;
                self.pop_var();
                
                write!(self.output, " }})) }}")?;
            }
            Term::App(f, a) => {
                // match f { Value::Func(f) => f(a), _ => panic!("App expects Func") }
                // We wrap this in a block to be safe
                write!(self.output, "(match ")?;
                self.emit(f)?;
                write!(self.output, " {{ Value::Func(f) => f(")?;
                self.emit(a)?;
                write!(self.output, "), _ => panic!(\"Expected Func\") }})")?;
            }
            Term::Pi(_, _) => {
                write!(self.output, "Value::Unit")?;
            }
            Term::LetE(_ty, val, body) => {
                // let x = val; body
                let var_name = self.fresh_var();
                write!(self.output, "{{ let {} = ", var_name)?;
                self.emit(val)?;
                write!(self.output, "; ")?;
                
                self.push_var(var_name);
                self.emit(body)?;
                self.pop_var();
                write!(self.output, " }}")?;
            }
            Term::Ind(name, _) => {
                 write!(self.output, "Value::Unit")?; // Type name -> Unit
            }
            Term::Ctor(name, idx, _) => {
                if name == "Nat" {
                    if *idx == 0 {
                        // zero
                        write!(self.output, "Value::Nat(0)")?;
                    } else if *idx == 1 {
                        // succ: |n| Nat(n+1)
                        write!(self.output, "Value::Func(Rc::new(|n| match n {{ Value::Nat(i) => Value::Nat(i+1), _ => panic!(\"succ expects Nat\") }}))")?;
                    } else {
                         return Err(anyhow!("Unknown Nat ctor: {}", idx));
                    }
                } else if name == "Bool" {
                     if *idx == 0 {
                         write!(self.output, "Value::Bool(true)")?;
                     } else if *idx == 1 {
                         write!(self.output, "Value::Bool(false)")?;
                     } else {
                         return Err(anyhow!("Unknown Bool ctor: {}", idx));
                     }
                } else if name == "List" {
                     if *idx == 0 {
                         write!(self.output, "Value::Func(Rc::new(|_| Value::List(Rc::new(List::Nil))))")?;
                     } else if *idx == 1 {
                         write!(self.output, "Value::Func(Rc::new(|_| Value::Func(Rc::new(|h| {{ let h=h.clone(); Value::Func(Rc::new(move |t| match t {{ Value::List(l) => Value::List(Rc::new(List::Cons(h.clone(), l))), _ => panic!(\"cons expects List\") }} )) }} ))))")?;
                     } else {
                         return Err(anyhow!("Unknown List ctor: {}", idx));
                     }
                } else {
                    // Generic Inductive Constructor
                    if let Some(decl) = self.inductives.get(name) {
                        if let Some(ctor) = decl.ctors.get(*idx) {
                             // Determine arity by counting Pi types
                             let mut arity = 0;
                             let mut curr = &ctor.ty;
                             while let Term::Pi(_, body) = &**curr {
                                 arity += 1;
                                 curr = body;
                             }
                             
                             if arity == 0 {
                                 write!(self.output, "Value::Inductive(\"{}\".to_string(), {}, vec![])", name, idx)?;
                             } else {
                                 // Generate nested closures
                                 // Value::Func(|a0| Value::Func(|a1| ... Value::Inductive(..., vec![a0, a1...]) ))
                                 for i in 0..arity {
                                     let arg_name = format!("arg_{}", i);
                                     write!(self.output, "Value::Func(Rc::new(move |{}: Value| {{ ", arg_name)?;
                                     if i < arity - 1 {
                                         write!(self.output, "let {} = {}.clone(); ", arg_name, arg_name)?;
                                     }
                                 }
                                 
                                 write!(self.output, "Value::Inductive(\"{}\".to_string(), {}, vec![", name, idx)?;
                                 for i in 0..arity {
                                     if i > 0 { write!(self.output, ", ")?; }
                                     write!(self.output, "arg_{}.clone()", i)?;
                                 }
                                 write!(self.output, "])")?;
                                 
                                 for _ in 0..arity {
                                     write!(self.output, " }}))")?;
                                 }
                             }
                        } else {
                            return Err(anyhow!("Constructor index out of bounds: {} for {}", idx, name));
                        }
                    } else {
                        return Err(anyhow!("Unknown Inductive type: {}", name));
                    }
                }
            }
            Term::Rec(name, _) => {
                if name == "Nat" {
                    write!(self.output, "Value::Func(Rc::new(rec_nat_entry))")?;
                } else if name == "Bool" {
                    write!(self.output, "Value::Func(Rc::new(rec_bool_entry))")?;
                } else if name == "List" {
                    write!(self.output, "Value::Func(Rc::new(rec_list_entry))")?;
                } else {
                     // Check if generic inductive exists
                     if self.inductives.contains_key(name) {
                         write!(self.output, "Value::Func(Rc::new(rec_{}_entry))", name)?;
                     } else {
                         return Err(anyhow!("Rec not implemented for {}", name));
                     }
                }
            }
             Term::Const(name, _) => {
                 write!(self.output, "{}()", Self::sanitize_name(name))?;
             }
        }
        Ok(())
    }

    fn sanitize_name(name: &str) -> String {
        match name {
            "true" | "false" | "if" | "else" | "match" | "let" | "fn" | "struct" | "enum" | "type" | "return" | 
            "loop" | "while" | "for" | "in" | "use" | "mod" | "crate" | "pub" | "impl" | "trait" | "where" | 
            "as" | "break" | "continue" | "unsafe" | "async" | "await" | "move" | "ref" | "mut" | "static" | "const" => {
                format!("r#{}", name)
            }
            _ => name.to_string(),
        }
    }

    pub fn generate_program(defs: Vec<(String, Term)>, main_term: Option<Term>, inductives: HashMap<String, InductiveDecl>) -> Result<String> {
        let inductives_iter = inductives.clone();
        let mut cg = Codegen::new(inductives);
        
        cg.output.push_str(r#"
#![allow(dead_code, unused_variables, unused_parens, unreachable_patterns)]
use std::rc::Rc;

#[derive(Clone)]
enum Value {
    Nat(u64),
    Bool(bool),
    Unit,
    List(Rc<List>),
    Func(Rc<dyn Fn(Value) -> Value>),
    Inductive(String, usize, Vec<Value>),
}

#[derive(Clone, Debug)]
enum List {
    Nil,
    Cons(Value, Rc<List>),
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nat(n) => write!(f, "Nat({})", n),
            Value::Bool(b) => write!(f, "Bool({})", b),
            Value::Unit => write!(f, "Unit"),
            Value::List(l) => write!(f, "{:?}", l),
            Value::Func(_) => write!(f, "<func>"),
            Value::Inductive(name, idx, args) => {
                write!(f, "{}", name)?;
                if !args.is_empty() {
                    write!(f, "(")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 { write!(f, ", ")?; }
                        write!(f, "{:?}", arg)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

// Recursion Helper for Nat
fn rec_nat_entry(motive: Value) -> Value {
    Value::Func(Rc::new(move |zero| {
        let zero = zero.clone();
        Value::Func(Rc::new(move |succ| {
            let zero = zero.clone();
            let succ = succ.clone();
            Value::Func(Rc::new(move |n| {
                rec_nat_impl(zero.clone(), succ.clone(), n)
            }))
        }))
    }))
}

fn rec_nat_impl(zero_case: Value, succ_case: Value, n_val: Value) -> Value {
    match n_val {
        Value::Nat(0) => zero_case,
        Value::Nat(n) => {
            let n_prev = Value::Nat(n - 1);
            let ih = rec_nat_impl(zero_case.clone(), succ_case.clone(), n_prev.clone());
            
            match succ_case {
                Value::Func(f1) => {
                    let res1 = f1(n_prev);
                    match res1 {
                        Value::Func(f2) => f2(ih),
                        _ => panic!("succ_case expected 2 args"),
                    }
                },
                _ => panic!("succ_case must be Func")
            }
        },
        _ => panic!("rec_nat expects Nat")
    }
}

// Recursion Helper for Bool (Case Analysis)
// Rec Bool motive true_case false_case b
fn rec_bool_entry(_motive: Value) -> Value {
    Value::Func(Rc::new(move |true_case| {
        let true_case = true_case.clone();
        Value::Func(Rc::new(move |false_case| {
            let true_case = true_case.clone();
            let false_case = false_case.clone();
            Value::Func(Rc::new(move |b| {
                match b {
                    Value::Bool(true) => true_case.clone(),
                    Value::Bool(false) => false_case.clone(),
                    _ => panic!("rec_bool expects Bool")
                }
        }))
    }))
    }))
}

// Recursion Helper for List
fn rec_list_entry(T_val: Value) -> Value {
    Value::Func(Rc::new(move |_M| {
        let T_val = T_val.clone();
        Value::Func(Rc::new(move |nil_case| {
            let T_val = T_val.clone();
            let nil_case = nil_case.clone();
            Value::Func(Rc::new(move |cons_case| {
                 let T_val = T_val.clone();
                 let nil_case = nil_case.clone();
                 let cons_case = cons_case.clone();
                 Value::Func(Rc::new(move |l_val| {
                     rec_list_impl(T_val.clone(), nil_case.clone(), cons_case.clone(), l_val)
                 }))
            }))
        }))
    }))
}

fn rec_list_impl(T_val: Value, nil_case: Value, cons_case: Value, l_val: Value) -> Value {
    match l_val {
        Value::List(l) => match &*l {
             List::Nil => {
                 // nil_case takes T
                 match nil_case {
                     Value::Func(f) => f(T_val),
                     _ => panic!("nil_case expects T, got {:?}", nil_case)
                 }
             },
             List::Cons(h, t_rc) => {
                 let t_val = Value::List(t_rc.clone());
                 let ih = rec_list_impl(T_val.clone(), nil_case.clone(), cons_case.clone(), t_val.clone());
                 // cons_case takes T, h, t, ih
                 match cons_case {
                     Value::Func(f1) => {
                         match f1(T_val) { // Apply T
                             Value::Func(f2) => match f2(h.clone()) { // Apply h
                                 Value::Func(f3) => match f3(t_val) { // Apply t
                                      Value::Func(f4) => f4(ih), // Apply ih
                                      _ => panic!("cons_case expects 4 args")
                                 },
                                 _ => panic!("cons_case expects 4 args")
                             },
                             _ => panic!("cons_case expects 4 args")
                         }
                     },
                     _ => panic!("cons_case must be Func")
                 }
             }
        },
        _ => panic!("Expected List")
    }
}
"#);
        
        // Emit definitions as functions
        for (name, val) in defs {
            cg.output.push_str("fn ");
            cg.output.push_str(&Self::sanitize_name(&name));
            cg.output.push_str("() -> Value {\n");
            cg.emit(&val)?;
            cg.output.push_str("\n}\n");
        }

        // Emit Generic Recursion Helpers
        for (ind_name, decl) in &inductives_iter {
            if ind_name == "Nat" || ind_name == "Bool" || ind_name == "List" { continue; }
            
            // rec_I_entry
            // Args: Params (k) -> Motive (1) -> MinorPremises (m) -> Major (1)
            // Total chain length
            // We need to count params.
            let mut num_params = 0;
            let mut curr = &decl.ty;
             while let Term::Pi(_, body) = &**curr {
                 num_params += 1;
                 curr = body;
             }
             // Actually, `decl.univ_params` is for Levels. `ty` Pi's are params + indices?
             // In LRL kernel, inductive params are usually part of `ty`.
             // But for `Rec`, we treat `Params` as arguments to `Rec`.
             // `Rec(I, params...)`.
             // In `codegen`, `Term::Rec` is just the eliminator.
             // It expects `num_params` args FIRST.
             // Then `motive`.
             // Then `constructors` (minor premises).
             // Then `major`.
             
             let num_ctors = decl.ctors.len();
             let total_args = num_params + 1 + num_ctors + 1;
             
             cg.output.push_str(&format!("// Rec for {}\n", ind_name));
             cg.output.push_str(&format!("fn rec_{}_entry(arg_0: Value) -> Value {{\n", ind_name));
             
             // Chain closures
             for i in 1..total_args {
                 cg.output.push_str(&format!("    Value::Func(Rc::new(move |arg_{}: Value| {{\n", i));
                 // Clone previous args to make them available
                 for j in 0..i {
                     cg.output.push_str(&format!("        let arg_{} = arg_{}.clone();\n", j, j));
                 }
             }
             
             // Call impl
             cg.output.push_str(&format!("        rec_{}_impl(", ind_name));
             for i in 0..total_args {
                 if i > 0 { cg.output.push_str(", "); }
                 cg.output.push_str(&format!("arg_{}", i));
             }
             cg.output.push_str(")\n");
             
             // Close closures
             for _ in 1..total_args {
                 cg.output.push_str("    }))\n");
             }
             cg.output.push_str("}\n\n");
             
             // rec_I_impl
             cg.output.push_str(&format!("fn rec_{}_impl(", ind_name));
              for i in 0..total_args {
                 if i > 0 { cg.output.push_str(", "); }
                 cg.output.push_str(&format!("arg_{}: Value", i));
             }
             cg.output.push_str(") -> Value {\n");
             
             // Identify arguments
             // arg_0 .. arg_{num_params-1} : Params
             // arg_{num_params} : Motive (ignored for computation)
             // arg_{num_params+1} .. arg_{num_params+num_ctors} : Minor Premises
             // arg_{total_args-1} : Major
             
             let major_idx = total_args - 1;
             let first_minor_idx = num_params + 1;
             
             cg.output.push_str(&format!("    match arg_{} {{\n", major_idx));
             cg.output.push_str(&format!("        Value::Inductive(n, idx, ctor_args) => {{\n"));
             cg.output.push_str(&format!("            if n != \"{}\" {{ panic!(\"rec_{} mismatch\"); }}\n", ind_name, ind_name));
             cg.output.push_str("            match idx {\n");
             
             for (c_idx, ctor) in decl.ctors.iter().enumerate() {
                 cg.output.push_str(&format!("                {} => {{\n", c_idx));
                 
                 // Apply minor premise `arg_{first_minor_idx + c_idx}`
                 // Arguments: ctor_args + recursive IHs
                 // We need to know ctor structure.
                 // Ctor params comes from `ctor.ty`.
                 // Skip `num_params` uniform parameters?
                 // `ctor.ty` includes `pi` for parameters?
                 // In LRL kernel, constructor types usually include the inductive parameters as first arguments.
                 // But in `Value::Inductive`, `ctor_args` usually ONLY contains the explicit constructor arguments?
                 // Let's verify.
                 // `add_inductive` in `repl.rs`: `ty` is fully qualified.
                 // `ctor.ty`: `Pi T ...`?
                 // If `List` is `Pi T Type Type`.
                 // `nil` is `Pi T Type List T`.
                 // My manual `cons` codegen expects `h`, `t`?
                 // Manual `cons` implementation:
                 // `rec_list_entry` takes `T_val` (param).
                 // `rec_list_impl` takes `T_val`.
                 // `nil_case` takes `T_val`.
                 // `cons_case` takes `T_val`, `h`, `t`, `ih`.
                 // `Value::List(Cons(h, t))` stores `h`. `t`.
                 // It does NOT store `T`.
                 // So `ctor_args` for `cons` are `[h, t]`.
                 // BUT `cons_case` expects `T` first.
                 // So we must pass `params` (arg_0..arg_{num_params}) to minor premise FIRST.
                 
                 let minor_idx = first_minor_idx + c_idx;
                 cg.output.push_str(&format!("                    // Apply minor premise {}\n", minor_idx));
                 
                 // Logic to apply minor premise to params + ctor_args + IHs
                 // We have `arg_{minor_idx}` as the function.
                 // We apply it to `arg_0` .. `arg_{num_params-1}`.
                 // Then apply to `ctor_args[k]`.
                 // Then apply `IH` if `ctor_args[k]` is recursive.
                 
                 // Helper to determine if type is recursive
                 // `ctor.ty` has structure `Pi P1.. Pi Pk.. Pi A1.. Pi An -> I ...`
                 // We need to skip `num_params` Pis.
                 let mut curr = &ctor.ty;
                 for _ in 0..num_params {
                     if let Term::Pi(_, b) = &**curr { curr = b; }
                 }
                 
                 // Now `curr` has arguments corresponding to `ctor_args`.
                 let mut arg_types = Vec::new();
                 while let Term::Pi(ty, b) = &**curr {
                     arg_types.push(ty.clone());
                     curr = b;
                 }
                 
                 // `arg_types` corresponds to `ctor_args`.
                 // Assert len match?
                 // cg.output.push_str("                    if ctor_args.len() != " + arg_types.len() + " { panic! }");
                 
                 // Generate application validation
                 cg.output.push_str(&format!("                    let mut curr_fn = arg_{}.clone();\n", minor_idx));
                 
                 // Apply Params
                 for p in 0..num_params {
                      cg.output.push_str(&format!("                    // Apply param {}\n", p));
                      cg.output.push_str(&format!("                    match curr_fn {{ Value::Func(f) => curr_fn = f(arg_{}.clone()), _ => panic!(\"param app\") }}\n", p));
                 }
                 
                 // Apply Args and IH
                 for (a_i, a_ty) in arg_types.iter().enumerate() {
                      cg.output.push_str(&format!("                    let val_{} = ctor_args[{}].clone();\n", a_i, a_i));
                      
                      // Check recursion
                      // Is `a_ty` == `Ind(ind_name)`?
                      // `a_ty` might be `App(Ind(name), ...)` or just `Ind(name)`.
                      let is_rec = if let Term::App(head, _) = &**a_ty {
                          if let Term::Ind(n, _) = &**head { n == ind_name } else { false }
                      } else if let Term::Ind(n, _) = &**a_ty {
                          n == ind_name
                      } else { false };
                      
                      // Apply val
                      cg.output.push_str(&format!("                    match curr_fn {{ Value::Func(f) => curr_fn = f(val_{}.clone()), _ => panic!(\"arg app\") }}\n", a_i));
                      
                      if is_rec {
                          // Compute IH
                          // ih = rec_I_impl(params..., params..., motive, minors..., val_{})
                          // Wait. `rec_I_impl` takes ALL args.
                          // arg_0..arg_{total-2} are same.
                          // only last arg (major) changes to `val_{}`.
                          cg.output.push_str(&format!("                    let ih_{} = rec_{}_impl(", a_i, ind_name));
                          for k in 0..total_args-1 {
                              cg.output.push_str(&format!("arg_{}.clone(), ", k));
                          }
                          cg.output.push_str(&format!("val_{}.clone());\n", a_i));
                          
                          // Apply IH
                          cg.output.push_str(&format!("                    match curr_fn {{ Value::Func(f) => curr_fn = f(ih_{}), _ => panic!(\"ih app\") }}\n", a_i));
                      }
                 }
                 
                 cg.output.push_str("                    curr_fn\n");
                 cg.output.push_str("                }\n");
             }
             
             cg.output.push_str("                _ => panic!(\"Invalid Ctor Index\"),\n");
             cg.output.push_str("            }\n"); // match idx
             cg.output.push_str("        }\n"); // match Value
             cg.output.push_str("        _ => panic!(\"Expected Inductive\"),\n");
             cg.output.push_str("    }\n"); // match Match
             cg.output.push_str("}\n\n");
        }

        cg.output.push_str("fn main() {\n");
        if let Some(main) = main_term {
             cg.output.push_str("    let result = ");
             cg.emit(&main)?;
             cg.output.push_str(";\n    println!(\"Result: {:?}\", result);\n");
        }
        
        cg.output.push_str("}\n"); // End main
        Ok(cg.output)
    }
}
