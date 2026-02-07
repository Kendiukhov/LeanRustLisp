use crate::{
    Body, CallOperand, Literal, Operand, Place, PlaceElem, RuntimeCheckKind, Rvalue, Statement,
    Terminator,
};
use kernel::ast::{InductiveDecl, Term};
use std::collections::HashMap;
use std::rc::Rc;

use kernel::checker::{Builtin, Env};

fn count_indices(ty: &Rc<Term>, num_params: usize) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(_, body, _, _) = &**current {
        count += 1;
        current = body;
    }
    if count >= num_params {
        count - num_params
    } else {
        0
    }
}

/// Check if a type is recursive (references the given inductive type).
fn is_recursive_arg(ty: &Rc<Term>, ind_name: &str) -> bool {
    match &**ty {
        Term::Ind(n, _) => n == ind_name,
        Term::App(f, _, _) => is_recursive_arg(f, ind_name),
        _ => false,
    }
}

pub fn codegen_recursors(inductives: &HashMap<String, InductiveDecl>, env: &Env) -> String {
    let mut code = String::new();
    for (ind_name, decl) in inductives {
        if env.is_builtin(Builtin::Nat, ind_name)
            || env.is_builtin(Builtin::Bool, ind_name)
            || env.is_builtin(Builtin::List, ind_name)
        {
            continue;
        }

        let num_params = decl.num_params;
        let num_ctors = decl.ctors.len();
        let num_indices = count_indices(&decl.ty, num_params);
        let total_args = num_params + 1 + num_ctors + num_indices + 1;

        // Entry point
        code.push_str(&format!(
            "fn rec_{}_entry(arg_0: Value) -> Value {{\n",
            ind_name
        ));
        for i in 1..total_args {
            code.push_str(&format!(
                "    Value::Func(Rc::new(move |arg_{}: Value| {{\n",
                i
            ));
            for j in 0..i {
                code.push_str(&format!("        let arg_{} = arg_{}.clone();\n", j, j));
            }
        }

        code.push_str(&format!("        rec_{}_impl(", ind_name));
        for i in 0..total_args {
            if i > 0 {
                code.push_str(", ");
            }
            code.push_str(&format!("arg_{}", i));
        }
        code.push_str(")\n");

        for _ in 1..total_args {
            code.push_str("    }))\n");
        }
        code.push_str("}\n\n");

        // Impl
        code.push_str(&format!("fn rec_{}_impl(", ind_name));
        for i in 0..total_args {
            if i > 0 {
                code.push_str(", ");
            }
            code.push_str(&format!("arg_{}: Value", i));
        }
        code.push_str(") -> Value {\n");

        let major_idx = total_args - 1;
        let first_minor_idx = num_params + 1;

        code.push_str(&format!("    match arg_{} {{\n", major_idx));
        code.push_str("        Value::Inductive(n, idx, ctor_args) => {\n");
        code.push_str(&format!(
            "            if n != \"{}\" {{ panic!(\"rec_{}: type mismatch\"); }}\n",
            ind_name, ind_name
        ));
        code.push_str("            match idx {\n");

        for (c_idx, ctor) in decl.ctors.iter().enumerate() {
            code.push_str(&format!("                {} => {{\n", c_idx));
            let minor_idx = first_minor_idx + c_idx;

            // Extract arg types
            let mut curr = &ctor.ty;
            for _ in 0..num_params {
                if let Term::Pi(_, b, _, _) = &**curr {
                    curr = b;
                }
            }
            let mut arg_types = Vec::new();
            while let Term::Pi(ty, b, _, _) = &**curr {
                arg_types.push(ty.clone());
                curr = b;
            }

            // Only require mutability when constructor arguments are present and
            // the recursor pipeline actually rewrites `curr_fn`.
            if arg_types.is_empty() {
                code.push_str(&format!(
                    "                    let curr_fn = arg_{}.clone();\n",
                    minor_idx
                ));
            } else {
                code.push_str(&format!(
                    "                    let mut curr_fn = arg_{}.clone();\n",
                    minor_idx
                ));
            }

            for (a_i, a_ty) in arg_types.iter().enumerate() {
                code.push_str(&format!(
                    "                    let val_{} = ctor_args[{}].clone();\n",
                    a_i, a_i
                ));
                let is_rec = is_recursive_arg(a_ty, ind_name);

                code.push_str(&format!("                    match curr_fn {{ Value::Func(f) => curr_fn = f(val_{}.clone()), _ => panic!(\"rec_{}: expected func\") }}\n", a_i, ind_name));

                if is_rec {
                    code.push_str(&format!(
                        "                    let ih_{} = rec_{}_impl(",
                        a_i, ind_name
                    ));
                    for k in 0..total_args - 1 {
                        code.push_str(&format!("arg_{}.clone(), ", k));
                    }
                    code.push_str(&format!("val_{}.clone());\n", a_i));

                    code.push_str(&format!("                    match curr_fn {{ Value::Func(f) => curr_fn = f(ih_{}), _ => panic!(\"rec_{}: expected func for IH\") }}\n", a_i, ind_name));
                }
            }
            code.push_str("                    curr_fn\n");
            code.push_str("                }\n");
        }

        code.push_str(&format!(
            "                _ => panic!(\"rec_{}: invalid ctor idx\"),\n",
            ind_name
        ));
        code.push_str("            }\n");
        code.push_str("        }\n");
        code.push_str(&format!(
            "        _ => panic!(\"rec_{}: expected Inductive\"),\n",
            ind_name
        ));
        code.push_str("    }\n");
        code.push_str("}\n");
    }
    code
}

/// Generates the unified runtime prelude (same as legacy codegen).
/// This includes the Value enum and all recursor helpers.
pub fn codegen_prelude() -> String {
    r#"
#![allow(non_snake_case, non_camel_case_types)]

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

fn runtime_refcell_borrow_check(_value: &Value) {
    // TODO: hook into RefCell runtime representation
}

fn runtime_mutex_lock(_value: &Value) {
    // TODO: hook into Mutex runtime representation
}

fn runtime_bounds_check(container: &Value, index: &Value) {
    let idx = match index {
        Value::Nat(n) => *n as usize,
        _ => return,
    };

    let Some(len) = container_len(container) else {
        return;
    };

    if idx >= len {
        panic!("index out of bounds");
    }
}

fn runtime_index(container: &Value, index: &Value) -> Value {
    let idx = match index {
        Value::Nat(n) => *n as usize,
        _ => return Value::Unit,
    };

    match container {
        Value::List(list) => list_nth(list, idx),
        Value::Inductive(name, _, args)
            if (name == "VecDyn" || name == "Slice" || name == "Array") =>
        {
            match args.get(0) {
                Some(Value::List(list)) => list_nth(list, idx),
                _ => Value::Unit,
            }
        }
        _ => Value::Unit,
    }
}

fn runtime_nat_to_char(value: &Value) -> Option<char> {
    match value {
        Value::Nat(n) => {
            if *n > u32::MAX as u64 {
                None
            } else {
                char::from_u32(*n as u32)
            }
        }
        _ => None,
    }
}

fn runtime_list_nat_to_string(list: &Rc<List>) -> String {
    let mut out = String::new();
    let mut current = list.clone();
    loop {
        match &*current {
            List::Nil => break,
            List::Cons(head, tail) => {
                match runtime_nat_to_char(head) {
                    Some(ch) => out.push(ch),
                    None => out.push('\u{FFFD}'),
                }
                current = tail.clone();
            }
        }
    }
    out
}

fn runtime_text_to_string(value: &Value) -> String {
    match value {
        Value::Inductive(name, idx, args) if name == "Text" && *idx == 0 => match args.first() {
            Some(Value::List(list)) => runtime_list_nat_to_string(list),
            _ => String::new(),
        },
        _ => format!("{:?}", value),
    }
}

fn runtime_string_to_list(input: &str) -> Rc<List> {
    let mut list = Rc::new(List::Nil);
    for ch in input.chars().rev() {
        list = Rc::new(List::Cons(Value::Nat(ch as u64), list));
    }
    list
}

fn runtime_string_to_text(input: &str) -> Value {
    Value::Inductive(
        "Text".to_string(),
        0,
        vec![Value::List(runtime_string_to_list(input))],
    )
}

fn runtime_print_nat(value: Value) -> Value {
    match &value {
        Value::Nat(n) => println!("{}", n),
        _ => println!("{:?}", value),
    }
    value
}

fn runtime_print_bool(value: Value) -> Value {
    match &value {
        Value::Bool(b) => println!("{}", b),
        _ => println!("{:?}", value),
    }
    value
}

fn runtime_print_text(value: Value) -> Value {
    println!("{}", runtime_text_to_string(&value));
    value
}

fn runtime_read_file_text(path: Value) -> Value {
    let path_string = runtime_text_to_string(&path);
    match std::fs::read_to_string(&path_string) {
        Ok(contents) => runtime_string_to_text(&contents),
        Err(err) => panic!("read_file failed for '{}': {}", path_string, err),
    }
}

fn runtime_write_file_text(path: Value, contents: Value) -> Value {
    let path_string = runtime_text_to_string(&path);
    let content_string = runtime_text_to_string(&contents);
    if let Err(err) = std::fs::write(&path_string, content_string.as_bytes()) {
        panic!("write_file failed for '{}': {}", path_string, err);
    }
    contents
}

fn runtime_result_to_string(value: &Value) -> String {
    match value {
        Value::Inductive(name, idx, _) if name == "Text" && *idx == 0 => runtime_text_to_string(value),
        Value::Func(_) => "<func>".to_string(),
        _ => format!("{:?}", value),
    }
}

fn list_len(list: &Rc<List>) -> usize {
    match &**list {
        List::Nil => 0,
        List::Cons(_, tail) => 1 + list_len(tail),
    }
}

fn list_nth(list: &Rc<List>, idx: usize) -> Value {
    match &**list {
        List::Nil => Value::Unit,
        List::Cons(head, tail) => {
            if idx == 0 {
                head.clone()
            } else {
                list_nth(tail, idx - 1)
            }
        }
    }
}

fn container_len(container: &Value) -> Option<usize> {
    match container {
        Value::List(list) => Some(list_len(list)),
        Value::Inductive(name, _, args)
            if (name == "VecDyn" || name == "Slice" || name == "Array") =>
        {
            match args.get(0) {
                Some(Value::List(list)) => Some(list_len(list)),
                _ => None,
            }
        }
        _ => None,
    }
}

fn runtime_discriminant(value: &Value) -> u64 {
    match value {
        Value::Nat(0) => 0,
        Value::Nat(_) => 1,
        Value::Bool(true) => 0,
        Value::Bool(false) => 1,
        Value::List(list) => match &**list {
            List::Nil => 0,
            List::Cons(_, _) => 1,
        },
        Value::Inductive(_, idx, _) => *idx as u64,
        _ => 0,
    }
}

fn runtime_project_field(value: &Value, downcast_idx: Option<usize>, field_idx: usize) -> Value {
    match value {
        Value::Nat(n) => {
            if let Some(idx) = downcast_idx {
                if idx != 1 {
                    panic!("Nat downcast mismatch: expected succ ctor");
                }
            }
            if field_idx == 0 && *n > 0 {
                Value::Nat(*n - 1)
            } else {
                panic!("Nat field projection out of shape");
            }
        }
        Value::List(list) => {
            if let Some(idx) = downcast_idx {
                if idx != 1 {
                    panic!("List downcast mismatch: expected cons ctor");
                }
            }
            match (&**list, field_idx) {
                (List::Cons(head, _), 0) => head.clone(),
                (List::Cons(_, tail), 1) => Value::List(tail.clone()),
                _ => panic!("List field projection out of shape"),
            }
        }
        Value::Inductive(_, idx, args) => {
            if let Some(expected) = downcast_idx {
                if expected != *idx {
                    panic!("inductive downcast mismatch");
                }
            }
            args.get(field_idx)
                .cloned()
                .unwrap_or_else(|| panic!("inductive field out of bounds"))
        }
        _ => panic!("Field access on unsupported runtime value"),
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
pub fn codegen_body(name: &str, body: &Body, closure_base: usize) -> String {
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
        let args = (1..=body.arg_count)
            .map(|i| format!("arg{}: Value", i))
            .collect::<Vec<_>>()
            .join(", ");
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
        code.push_str(&codegen_block(block, is_closure, closure_base));
        code.push_str("            }\n");
    }

    code.push_str("            _ => break,\n");
    code.push_str("        }\n");
    code.push_str("    }\n");
    code.push_str("    _0\n");
    code.push_str("}\n");

    code
}

fn codegen_block(data: &crate::BasicBlockData, is_closure: bool, closure_base: usize) -> String {
    let mut code = String::new();

    for stmt in &data.statements {
        code.push_str(&codegen_statement(stmt, is_closure, closure_base));
    }

    if let Some(term) = &data.terminator {
        code.push_str(&codegen_terminator(term, is_closure, closure_base));
    }

    code
}

fn codegen_statement(stmt: &Statement, is_closure: bool, closure_base: usize) -> String {
    match stmt {
        Statement::Assign(place, rvalue) => {
            let dest = codegen_place_assign(place);
            let val = codegen_rvalue(rvalue, is_closure, closure_base);
            format!("                {} = {};\n", dest, val)
        }
        Statement::RuntimeCheck(check) => codegen_runtime_check(check, is_closure),
        Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {
            format!("                // {:?}\n", stmt)
        }
    }
}

fn codegen_runtime_check(check: &RuntimeCheckKind, is_closure: bool) -> String {
    match check {
        RuntimeCheckKind::RefCellBorrow { local } => {
            let value = codegen_place_read(&Place::from(*local), is_closure);
            format!(
                "                runtime_refcell_borrow_check(&{});\n",
                value
            )
        }
        RuntimeCheckKind::MutexLock { local } => {
            let value = codegen_place_read(&Place::from(*local), is_closure);
            format!("                runtime_mutex_lock(&{});\n", value)
        }
        RuntimeCheckKind::BoundsCheck { local, index } => {
            let container = codegen_place_read(&Place::from(*local), is_closure);
            let idx = codegen_place_read(&Place::from(*index), is_closure);
            format!(
                "                runtime_bounds_check(&{}, &{});\n",
                container, idx
            )
        }
    }
}

fn codegen_terminator(term: &Terminator, is_closure: bool, closure_base: usize) -> String {
    match term {
        Terminator::Return => "                break;\n".to_string(),
        Terminator::Goto { target } => {
            format!(
                "                state = {};\n                continue;\n",
                target.index()
            )
        }
        Terminator::SwitchInt { discr, targets } => {
            // Switch on discriminant
            let val = codegen_operand(discr, is_closure, closure_base);
            let mut code = format!("                match runtime_discriminant(&{}) {{\n", val);
            for (v_idx, val) in targets.values.iter().enumerate() {
                let target = targets.targets[v_idx];
                code.push_str(&format!(
                    "                    {} => {{ state = {}; continue; }}\n",
                    val,
                    target.index()
                ));
            }
            if targets.targets.len() > targets.values.len() {
                let default_target = targets.targets.last().unwrap();
                code.push_str(&format!(
                    "                    _ => {{ state = {}; continue; }}\n",
                    default_target.index()
                ));
            } else {
                code.push_str("                    _ => unreachable!(),\n");
            }
            code.push_str("                }\n");
            code
        }
        Terminator::Call {
            func,
            args,
            destination,
            target,
        } => {
            let func_str = codegen_call_operand(func, is_closure, closure_base);
            // Expect func to be Value::Func
            // args should be length 1
            let arg_str = if !args.is_empty() {
                codegen_operand(&args[0], is_closure, closure_base)
            } else {
                "Value::Unit".to_string()
            };

            let dest = codegen_place_assign(destination);

            let mut code = format!(
                "                {} = match {} {{ Value::Func(f) => f({}), _ => panic!(\"Expected Func\") }};\n",
                dest, func_str, arg_str
            );

            if let Some(t) = target {
                code.push_str(&format!(
                    "                state = {};\n                continue;\n",
                    t.index()
                ));
            } else {
                code.push_str("                break;\n");
            }
            code
        }
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
    let mut pending_downcast: Option<usize> = None;
    for proj in &place.projection {
        match proj {
            PlaceElem::Field(i) => {
                let downcast = match pending_downcast {
                    Some(idx) => format!("Some({})", idx),
                    None => "None".to_string(),
                };
                s = format!("runtime_project_field(&{}, {}, {})", s, downcast, i);
                pending_downcast = None;
            }
            PlaceElem::Downcast(idx) => {
                // Keep the downcast ctor index so field projections on builtin
                // representations (Nat/List) can be interpreted soundly.
                pending_downcast = Some(*idx);
            }
            PlaceElem::Deref => {
                // Deref - just clone the value
                s = format!("{}.clone()", s);
            }
            PlaceElem::Index(index_local) => {
                let idx = codegen_place_read(&Place::from(*index_local), is_closure);
                s = format!("runtime_index(&{}, &{})", s, idx);
                pending_downcast = None;
            }
        }
    }
    s
}

fn codegen_rvalue(rvalue: &Rvalue, is_closure: bool, closure_base: usize) -> String {
    match rvalue {
        Rvalue::Use(op) => codegen_operand(op, is_closure, closure_base),
        Rvalue::Ref(_, place) => {
            // Dynamic backend models references as value snapshots.
            // Always clone so repeated borrows across loop iterations do not move locals.
            let value = codegen_place_read(place, is_closure);
            format!("{}.clone()", value)
        }
        Rvalue::Discriminant(place) => {
            // Return discriminant value as Nat for SwitchInt
            let p = codegen_place_read(place, is_closure);
            format!("Value::Nat(runtime_discriminant(&{}))", p)
        }
    }
}

fn codegen_operand(op: &Operand, is_closure: bool, closure_base: usize) -> String {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let s = codegen_place_read(place, is_closure);
            format!("{}.clone()", s)
        }
        Operand::Constant(c) => codegen_constant(&c.literal, closure_base),
    }
}

fn codegen_call_operand(op: &CallOperand, is_closure: bool, closure_base: usize) -> String {
    match op {
        CallOperand::Operand(op) => codegen_operand(op, is_closure, closure_base),
        CallOperand::Borrow(_, place) => {
            let s = codegen_place_read(place, is_closure);
            format!("{}.clone()", s)
        }
    }
}

pub fn codegen_constant(lit: &Literal, closure_base: usize) -> String {
    match lit {
        Literal::Unit => "Value::Unit".to_string(),
        Literal::Nat(n) => format!("Value::Nat({})", n),
        Literal::Bool(b) => format!("Value::Bool({})", b),
        Literal::GlobalDef(name) => match name.as_str() {
            "print_nat" => "Value::Func(Rc::new(|n| runtime_print_nat(n)))".to_string(),
            "print_bool" => "Value::Func(Rc::new(|b| runtime_print_bool(b)))".to_string(),
            "print_text" | "print" => {
                "Value::Func(Rc::new(|t| runtime_print_text(t)))".to_string()
            }
            "read_file" => "Value::Func(Rc::new(|path| runtime_read_file_text(path)))".to_string(),
            "write_file" => "Value::Func(Rc::new(|path| { let path = path.clone(); Value::Func(Rc::new(move |contents| runtime_write_file_text(path.clone(), contents))) }))".to_string(),
            _ => format!("{}()", sanitize_name(name)),
        },
        Literal::Recursor(name) => {
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
        Literal::OpaqueConst(reason) => format!(
            "panic!({:?})",
            format!("OpaqueConst literal reached codegen: {}", reason)
        ),
        Literal::Closure(idx, captures) => {
            // Generate a Value::Func that wraps the closure function
            // The closure function expects (env: Vec<Value>, arg: Value) -> Value
            // We capture the environment as a Vec and call the function
            let func_name = format!("closure_{}", closure_base + idx);
            if captures.is_empty() {
                // No captures - simple wrapper
                format!(
                    "Value::Func(Rc::new(move |arg| {}(vec![], arg)))",
                    func_name
                )
            } else {
                // Clone captures for the move closure
                // Note: captures are operands from the outer scope, not inside a closure
                let cap_clones: Vec<String> = captures
                    .iter()
                    .enumerate()
                    .map(|(i, op)| {
                        format!(
                            "let __cap{} = {}.clone();",
                            i,
                            codegen_operand(op, false, closure_base)
                        )
                    })
                    .collect();
                let cap_vec: Vec<String> = (0..captures.len())
                    .map(|i| format!("__cap{}.clone()", i))
                    .collect();
                format!(
                    "{{ {} Value::Func(Rc::new(move |arg| {}(vec![{}], arg))) }}",
                    cap_clones.join(" "),
                    func_name,
                    cap_vec.join(", ")
                )
            }
        }
        Literal::Fix(idx, captures) => {
            // Recursive closure: env[0] is self, env[1..] are captures
            let func_name = format!("closure_{}", closure_base + idx);
            if captures.is_empty() {
                format!("Value::Func(Rc::new_cyclic(|self_ref| {{ let self_val = Value::Func(self_ref.clone()); move |arg| {}(vec![self_val.clone()], arg) }}))", func_name)
            } else {
                let cap_clones: Vec<String> = captures
                    .iter()
                    .enumerate()
                    .map(|(i, op)| {
                        format!(
                            "let __cap{} = {}.clone();",
                            i,
                            codegen_operand(op, false, closure_base)
                        )
                    })
                    .collect();
                let cap_vec: Vec<String> = (0..captures.len())
                    .map(|i| format!("__cap{}.clone()", i))
                    .collect();
                format!("{{ {} Value::Func(Rc::new_cyclic(|self_ref| {{ let self_val = Value::Func(self_ref.clone()); let __env = vec![self_val.clone(), {}]; move |arg| {}(__env.clone(), arg) }})) }}",
                    cap_clones.join(" "),
                    cap_vec.join(", "),
                    func_name
                )
            }
        }
        Literal::InductiveCtor(ctor, arity) => {
            let adt = &ctor.adt;
            if adt.is_builtin(Builtin::Nat) {
                if ctor.index == 0 {
                    "Value::Nat(0)".to_string()
                } else {
                    "Value::Func(Rc::new(|n| match n { Value::Nat(i) => Value::Nat(i+1), _ => panic!(\"succ expects Nat\") }))".to_string()
                }
            } else if adt.is_builtin(Builtin::Bool) {
                if ctor.index == 0 {
                    "Value::Bool(true)".to_string()
                } else {
                    "Value::Bool(false)".to_string()
                }
            } else if adt.is_builtin(Builtin::List) {
                if ctor.index == 0 {
                    "Value::Func(Rc::new(|_| Value::List(Rc::new(List::Nil))))".to_string()
                } else {
                    "Value::Func(Rc::new(|_| Value::Func(Rc::new(|h| { let h = h.clone(); Value::Func(Rc::new(move |t| match t { Value::List(l) => Value::List(Rc::new(List::Cons(h.clone(), l))), _ => panic!(\"cons expects List\") })) }))))".to_string()
                }
            } else {
                let name = adt.name();
                if *arity == 0 {
                    format!(
                        "Value::Inductive(\"{}\".to_string(), {}, vec![])",
                        name, ctor.index
                    )
                } else {
                    let mut s = String::new();
                    for i in 0..*arity {
                        s.push_str(&format!("Value::Func(Rc::new(move |a{}| {{\n", i));
                        for j in 0..=i {
                            s.push_str(&format!("let a{} = a{}.clone();\n", j, j));
                        }
                    }

                    s.push_str(&format!(
                        "Value::Inductive(\"{}\".to_string(), {}, vec![",
                        name, ctor.index
                    ));
                    for i in 0..*arity {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&format!("a{}", i));
                    }
                    s.push_str("])\n");

                    for _ in 0..*arity {
                        s.push_str("}))\n");
                    }
                    s
                }
            }
        }
    }
}

pub fn sanitize_name(name: &str) -> String {
    let mut sanitized = String::new();

    for (idx, ch) in name.chars().enumerate() {
        let is_ident_char = if idx == 0 {
            ch.is_ascii_alphabetic() || ch == '_'
        } else {
            ch.is_ascii_alphanumeric() || ch == '_'
        };

        if is_ident_char {
            sanitized.push(ch);
        } else {
            if sanitized.is_empty() {
                sanitized.push('_');
            }
            sanitized.push_str(&format!("u{:X}", ch as u32));
            sanitized.push('_');
        }
    }

    if sanitized.is_empty() {
        sanitized.push('_');
    }

    match sanitized.as_str() {
        "true" | "false" | "if" | "else" | "match" | "let" | "fn" | "struct" | "enum" | "type"
        | "return" | "loop" | "while" | "for" | "in" | "use" | "mod" | "crate" | "pub" | "impl"
        | "trait" | "where" | "as" | "break" | "continue" | "unsafe" | "async" | "await"
        | "move" | "ref" | "mut" | "static" | "const" => {
            format!("r#{}", sanitized)
        }
        _ => sanitized,
    }
}

#[cfg(test)]
mod tests {
    use super::sanitize_name;

    #[test]
    fn sanitize_name_supports_symbol_operators() {
        assert_eq!(sanitize_name("+"), "_u2B_");
        assert_eq!(sanitize_name("-"), "_u2D_");
        assert_eq!(sanitize_name("*"), "_u2A_");
        assert_eq!(sanitize_name("/"), "_u2F_");
    }

    #[test]
    fn sanitize_name_preserves_plain_identifiers() {
        assert_eq!(sanitize_name("entry"), "entry");
        assert_eq!(sanitize_name("foo.bar"), "foou2E_bar");
    }
}
