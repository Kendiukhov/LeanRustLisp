use crate::{Body, BasicBlock, Statement, Terminator, Operand, Rvalue, Place, Literal, Local, PlaceElem};
use kernel::ast::Term;
use std::rc::Rc;

/// Generates the unified runtime prelude (same as legacy codegen).
/// This includes the Value enum and all recursor helpers.
pub fn codegen_prelude() -> String {
    r#"
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
fn rec_list_entry(t_val: Value) -> Value {
    Value::Func(Rc::new(move |_m| {
        let t_val = t_val.clone();
        Value::Func(Rc::new(move |nil_case| {
            let t_val = t_val.clone();
            let nil_case = nil_case.clone();
            Value::Func(Rc::new(move |cons_case| {
                 let t_val = t_val.clone();
                 let nil_case = nil_case.clone();
                 let cons_case = cons_case.clone();
                 Value::Func(Rc::new(move |l_val| {
                     rec_list_impl(t_val.clone(), nil_case.clone(), cons_case.clone(), l_val)
                 }))
            }))
        }))
    }))
}

fn rec_list_impl(t_val: Value, nil_case: Value, cons_case: Value, l_val: Value) -> Value {
    match l_val {
        Value::List(l) => match &*l {
             List::Nil => nil_case,
             List::Cons(h, t_rc) => {
                 let t_val_inner = Value::List(t_rc.clone());
                 let ih = rec_list_impl(t_val.clone(), nil_case.clone(), cons_case.clone(), t_val_inner.clone());
                 match cons_case {
                     Value::Func(f2) => match f2(h.clone()) {
                         Value::Func(f3) => match f3(t_val_inner) {
                              Value::Func(f4) => f4(ih),
                              _ => panic!("cons_case expects 3 args")
                         },
                         _ => panic!("cons_case expects 3 args")
                     },
                     _ => panic!("cons_case must be Func")
                 }
             }
        },
        _ => panic!("Expected List")
    }
}
"#.to_string()
}

/// Generates Rust code for a MIR Body using a state-machine approach.
pub fn codegen_body(name: &str, body: &Body) -> String {
    let mut code = String::new();

    // Determine if this is a closure (has 2 args: env + arg)
    let is_closure = body.arg_count == 2 && name.starts_with("closure_");

    // Function signature
    let sig = if body.arg_count == 0 {
        format!("fn {}() -> Value", name)
    } else if is_closure {
        // Closures take Vec<Value> for env to avoid wrapping
        format!("fn {}(__env: Vec<Value>, __arg: Value) -> Value", name)
    } else {
        // Generic multi-arg function
        let args = (1..=body.arg_count).map(|i| format!("arg{}: Value", i)).collect::<Vec<_>>().join(", ");
        format!("fn {}({}) -> Value", name, args)
    };

    code.push_str(&format!("{} {{\n", sig));

    // Declare locals
    code.push_str("    let mut state = 0;\n");
    // _0 is return place
    code.push_str("    let mut _0: Value = Value::Unit;\n");

    // Initialize args locals
    if is_closure {
        // _1 is not used directly, captures are unpacked from __env
        // _2 is the argument
        code.push_str("    let mut _1: Value = Value::Unit; // env placeholder\n");
        code.push_str("    let mut _2: Value = __arg;\n");
    } else if body.arg_count > 0 {
        for i in 1..=body.arg_count {
            code.push_str(&format!("    let mut _{}: Value = arg{};\n", i, i));
        }
    }

    // Declare other locals
    for i in (body.arg_count + 1)..body.local_decls.len() {
        code.push_str(&format!("    let mut _{}: Value = Value::Unit;\n", i));
    }

    code.push_str("\n    loop {\n");
    code.push_str("        match state {\n");

    for (idx, block) in body.basic_blocks.iter().enumerate() {
        code.push_str(&format!("            {} => {{\n", idx));
        code.push_str(&codegen_block(block, is_closure));
        code.push_str("            }\n");
    }

    code.push_str("            _ => break,\n");
    code.push_str("        }\n");
    code.push_str("    }\n");
    code.push_str("    _0\n");
    code.push_str("}\n");

    code
}

fn codegen_block(data: &crate::BasicBlockData, is_closure: bool) -> String {
    let mut code = String::new();

    for stmt in &data.statements {
        code.push_str(&codegen_statement(stmt, is_closure));
    }

    if let Some(term) = &data.terminator {
        code.push_str(&codegen_terminator(term, is_closure));
    }

    code
}

fn codegen_statement(stmt: &Statement, is_closure: bool) -> String {
    match stmt {
        Statement::Assign(place, rvalue) => {
            let dest = codegen_place_assign(place);
            let val = codegen_rvalue(rvalue, is_closure);
            format!("                {} = {};\n", dest, val)
        },
        Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {
            format!("                // {:?}\n", stmt)
        }
    }
}

fn codegen_terminator(term: &Terminator, is_closure: bool) -> String {
    match term {
        Terminator::Return => {
            "                break;\n".to_string()
        },
        Terminator::Goto { target } => {
            format!("                state = {};\n                continue;\n", target.index())
        },
        Terminator::SwitchInt { discr, targets } => {
            // Switch on discriminant
            let val = codegen_operand(discr, is_closure);
            let mut code = format!("                match (match &{} {{ Value::Nat(n) => *n, _ => 0 }}) {{\n", val);
            for (v_idx, val) in targets.values.iter().enumerate() {
                let target = targets.targets[v_idx];
                code.push_str(&format!("                    {} => {{ state = {}; continue; }}\n", val, target.index()));
            }
            if targets.targets.len() > targets.values.len() {
                 let default_target = targets.targets.last().unwrap();
                 code.push_str(&format!("                    _ => {{ state = {}; continue; }}\n", default_target.index()));
            } else {
                 code.push_str("                    _ => unreachable!(),\n");
            }
            code.push_str("                }\n");
            code
        },
        Terminator::Call { func, args, destination, target } => {
            let func_str = codegen_operand(func, is_closure);
            // Expect func to be Value::Func
            // args should be length 1
            let arg_str = if !args.is_empty() {
                codegen_operand(&args[0], is_closure)
            } else {
                "Value::Unit".to_string()
            };

            let dest = codegen_place_assign(destination);

            let mut code = format!(
                "                {} = match {} {{ Value::Func(f) => f({}), _ => panic!(\"Expected Func\") }};\n",
                dest, func_str, arg_str
            );

            if let Some(t) = target {
                 code.push_str(&format!("                state = {};\n                continue;\n", t.index()));
            } else {
                 code.push_str("                break;\n");
            }
            code
        },
        Terminator::Unreachable => "                unreachable!();\n".to_string(),
    }
}

fn codegen_place_assign(place: &Place) -> String {
    // For assignment, we usually assign to the local.
    // Projections in Dest? `_1.0 = ...`.
    // LRL MIR lowering doesn't seem to assign to fields (only reads).
    format!("_{}", place.local.index())
}

fn codegen_place_read(place: &Place, is_closure: bool) -> String {
    let local_idx = place.local.index();

    // Check if we're reading from env (_1) in a closure with field projection
    if is_closure && local_idx == 1 && !place.projection.is_empty() {
        // Reading a captured value from the environment
        for proj in &place.projection {
            if let PlaceElem::Field(i) = proj {
                return format!("__env[{}].clone()", i);
            }
        }
    }

    let mut s = format!("_{}", local_idx);
    for proj in &place.projection {
        match proj {
            PlaceElem::Field(i) => {
                // For Inductive types, access args vector
                s = format!("(match &{} {{ Value::Inductive(_, _, args) => args[{}].clone(), _ => panic!(\"Field access on non-inductive\") }})", s, i);
            }
            PlaceElem::Downcast(_) => {
                // Ignore downcast - we handle via discriminant separately
            }
            PlaceElem::Deref => {
                // Deref - just clone the value
                s = format!("{}.clone()", s);
            }
        }
    }
    s
}

fn codegen_rvalue(rvalue: &Rvalue, is_closure: bool) -> String {
    match rvalue {
        Rvalue::Use(op) => codegen_operand(op, is_closure),
        Rvalue::Ref(_, place) => {
            // Value is Clone, so we just copy
            codegen_place_read(place, is_closure)
        },
        Rvalue::Discriminant(place) => {
            // Return discriminant value as Nat for SwitchInt
            let p = codegen_place_read(place, is_closure);
            format!("(match &{} {{ Value::Nat(n) => Value::Nat(*n), Value::Bool(true) => Value::Nat(1), Value::Bool(false) => Value::Nat(0), Value::Inductive(_, idx, _) => Value::Nat(*idx as u64), _ => Value::Nat(0) }})", p)
        }
    }
}

fn codegen_operand(op: &Operand, is_closure: bool) -> String {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let s = codegen_place_read(place, is_closure);
            if matches!(op, Operand::Copy(_)) {
                 format!("{}.clone()", s)
            } else {
                 s // Move semantics (Value is Clone in Rust)
            }
        },
        Operand::Constant(c) => codegen_constant(&c.literal),
    }
}

fn codegen_constant(lit: &Literal) -> String {
    match lit {
        Literal::Nat(n) => format!("Value::Nat({})", n),
        Literal::Bool(b) => format!("Value::Bool({})", b),
        Literal::Closure(idx, captures) => {
            // Generate a Value::Func that wraps the closure function
            // The closure function expects (env: Vec<Value>, arg: Value) -> Value
            // We capture the environment as a Vec and call the function
            let func_name = format!("closure_{}", idx);
            if captures.is_empty() {
                // No captures - simple wrapper
                format!("Value::Func(Rc::new(move |arg| {}(vec![], arg)))", func_name)
            } else {
                // Clone captures for the move closure
                // Note: captures are operands from the outer scope, not inside a closure
                let cap_clones: Vec<String> = captures.iter().enumerate()
                    .map(|(i, op)| format!("let __cap{} = {}.clone();", i, codegen_operand(op, false)))
                    .collect();
                let cap_vec: Vec<String> = (0..captures.len())
                    .map(|i| format!("__cap{}.clone()", i))
                    .collect();
                format!("{{ {} Value::Func(Rc::new(move |arg| {}(vec![{}], arg))) }}",
                    cap_clones.join(" "),
                    func_name,
                    cap_vec.join(", ")
                )
            }
        },
        Literal::Term(t) => {
            match &**t {
                Term::Sort(_) => "Value::Unit".to_string(),
                Term::Const(n, _) => {
                     // Reference to another top-level Value definition
                     format!("{}()", sanitize_name(n))
                }
                Term::Ctor(name, idx, _) => {
                    // Constructor - generate appropriate value
                    if name == "Nat" {
                        if *idx == 0 {
                            "Value::Nat(0)".to_string()
                        } else {
                            "Value::Func(Rc::new(|n| match n { Value::Nat(i) => Value::Nat(i+1), _ => panic!(\"succ expects Nat\") }))".to_string()
                        }
                    } else if name == "Bool" {
                        if *idx == 0 {
                            "Value::Bool(true)".to_string()
                        } else {
                            "Value::Bool(false)".to_string()
                        }
                    } else if name == "List" {
                        if *idx == 0 {
                            "Value::Func(Rc::new(|_| Value::List(Rc::new(List::Nil))))".to_string()
                        } else {
                            "Value::Func(Rc::new(|_| Value::Func(Rc::new(|h| { let h = h.clone(); Value::Func(Rc::new(move |t| match t { Value::List(l) => Value::List(Rc::new(List::Cons(h.clone(), l))), _ => panic!(\"cons expects List\") })) }))))".to_string()
                        }
                    } else {
                        // Generic inductive constructor
                        format!("Value::Inductive(\"{}\".to_string(), {}, vec![])", name, idx)
                    }
                }
                Term::Rec(name, _) => {
                    // Recursor - return the entry function
                    if name == "Nat" {
                        "Value::Func(Rc::new(rec_nat_entry))".to_string()
                    } else if name == "Bool" {
                        "Value::Func(Rc::new(rec_bool_entry))".to_string()
                    } else if name == "List" {
                        "Value::Func(Rc::new(rec_list_entry))".to_string()
                    } else {
                        format!("Value::Func(Rc::new(rec_{}_entry))", name)
                    }
                }
                _ => "Value::Unit".to_string(),
            }
        }
    }
}

fn sanitize_name(name: &str) -> String {
    match name {
        "true" | "false" | "if" | "else" | "match" | "let" | "fn" | "struct" | "enum" | "type" | "return" |
        "loop" | "while" | "for" | "in" | "use" | "mod" | "crate" | "pub" | "impl" | "trait" | "where" |
        "as" | "break" | "continue" | "unsafe" | "async" | "await" | "move" | "ref" | "mut" | "static" | "const" => {
            format!("r#{}", name)
        }
        _ => name.replace(".", "_")
    }
}
