
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
                 // nil_case
                 nil_case
             },
             List::Cons(h, t_rc) => {
                 let t_val = Value::List(t_rc.clone());
                 let ih = rec_list_impl(T_val.clone(), nil_case.clone(), cons_case.clone(), t_val.clone());
                 // cons_case takes h, t, ih
                 match cons_case {
                     Value::Func(f2) => match f2(h.clone()) { // Apply h
                         Value::Func(f3) => match f3(t_val) { // Apply t
                              Value::Func(f4) => f4(ih), // Apply ih
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
fn zero() -> Value {
Value::Nat(0)
}
fn succ() -> Value {
Value::Func(Rc::new(|n| match n { Value::Nat(i) => Value::Nat(i+1), _ => panic!("succ expects Nat") }))
}
fn r#true() -> Value {
Value::Bool(true)
}
fn r#false() -> Value {
Value::Bool(false)
}
fn add() -> Value {
{ Value::Func(Rc::new(move |x_0: Value| { { let x_0 = x_0.clone(); Value::Func(Rc::new(move |x_1: Value| { (match (match (match (match Value::Func(Rc::new(rec_nat_entry)) { Value::Func(f) => f({ let x_0 = x_0.clone(); let x_1 = x_1.clone(); Value::Func(Rc::new(move |x_2: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_1.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f({ let x_0 = x_0.clone(); let x_1 = x_1.clone(); Value::Func(Rc::new(move |x_3: Value| { { let x_0 = x_0.clone(); let x_1 = x_1.clone(); let x_3 = x_3.clone(); Value::Func(Rc::new(move |x_4: Value| { (match succ() { Value::Func(f) => f(x_4.clone()), _ => panic!("Expected Func") }) })) } })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_0.clone()), _ => panic!("Expected Func") }) })) } })) }
}
fn not() -> Value {
{ Value::Func(Rc::new(move |x_5: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_5 = x_5.clone(); Value::Func(Rc::new(move |x_6: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#false()), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#true()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_5.clone()), _ => panic!("Expected Func") }) })) }
}
fn if_nat() -> Value {
{ Value::Func(Rc::new(move |x_7: Value| { { let x_7 = x_7.clone(); Value::Func(Rc::new(move |x_8: Value| { { let x_7 = x_7.clone(); let x_8 = x_8.clone(); Value::Func(Rc::new(move |x_9: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_7 = x_7.clone(); let x_8 = x_8.clone(); let x_9 = x_9.clone(); Value::Func(Rc::new(move |x_10: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_8.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_9.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_7.clone()), _ => panic!("Expected Func") }) })) } })) } })) }
}
fn and() -> Value {
{ Value::Func(Rc::new(move |x_11: Value| { { let x_11 = x_11.clone(); Value::Func(Rc::new(move |x_12: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_11 = x_11.clone(); let x_12 = x_12.clone(); Value::Func(Rc::new(move |x_13: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_12.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#false()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_11.clone()), _ => panic!("Expected Func") }) })) } })) }
}
fn or() -> Value {
{ Value::Func(Rc::new(move |x_14: Value| { { let x_14 = x_14.clone(); Value::Func(Rc::new(move |x_15: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_14 = x_14.clone(); let x_15 = x_15.clone(); Value::Func(Rc::new(move |x_16: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#true()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_15.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_14.clone()), _ => panic!("Expected Func") }) })) } })) }
}
fn nil() -> Value {
Value::Func(Rc::new(|_| Value::List(Rc::new(List::Nil))))
}
fn cons() -> Value {
Value::Func(Rc::new(|_| Value::Func(Rc::new(|h| { let h=h.clone(); Value::Func(Rc::new(move |t| match t { Value::List(l) => Value::List(Rc::new(List::Cons(h.clone(), l))), _ => panic!("cons expects List") } )) } ))))
}
fn ret() -> Value {
Value::Func(Rc::new(move |arg_0: Value| { let arg_0 = arg_0.clone(); Value::Func(Rc::new(move |arg_1: Value| { let arg_0 = arg_0.clone(); let arg_1 = arg_1.clone(); Value::Inductive("Comp".to_string(), 0, vec![arg_0, arg_1]) })) }))
}
fn bind() -> Value {
Value::Func(Rc::new(move |arg_0: Value| { let arg_0 = arg_0.clone(); Value::Func(Rc::new(move |arg_1: Value| { let arg_0 = arg_0.clone(); let arg_1 = arg_1.clone(); Value::Func(Rc::new(move |arg_2: Value| { let arg_0 = arg_0.clone(); let arg_1 = arg_1.clone(); let arg_2 = arg_2.clone(); Value::Func(Rc::new(move |arg_3: Value| { let arg_0 = arg_0.clone(); let arg_1 = arg_1.clone(); let arg_2 = arg_2.clone(); let arg_3 = arg_3.clone(); Value::Inductive("Comp".to_string(), 1, vec![arg_0, arg_1, arg_2, arg_3]) })) })) })) }))
}
fn refl() -> Value {
Value::Func(Rc::new(move |arg_0: Value| { let arg_0 = arg_0.clone(); Value::Func(Rc::new(move |arg_1: Value| { let arg_0 = arg_0.clone(); let arg_1 = arg_1.clone(); Value::Inductive("Eq".to_string(), 0, vec![arg_0, arg_1]) })) }))
}
// Generic Recursor for Eq
// Layout: 3 params, 1 motive, 1 minors, 1 major = 6 total
fn rec_Eq_entry(arg_0: Value) -> Value {
    Value::Func(Rc::new(move |arg_1: Value| {
        let arg_0 = arg_0.clone();
    Value::Func(Rc::new(move |arg_2: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
    Value::Func(Rc::new(move |arg_3: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        let arg_2 = arg_2.clone();
    Value::Func(Rc::new(move |arg_4: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        let arg_2 = arg_2.clone();
        let arg_3 = arg_3.clone();
    Value::Func(Rc::new(move |arg_5: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        let arg_2 = arg_2.clone();
        let arg_3 = arg_3.clone();
        let arg_4 = arg_4.clone();
        rec_Eq_impl(arg_0, arg_1, arg_2, arg_3, arg_4, arg_5)
    }))
    }))
    }))
    }))
    }))
}

fn rec_Eq_impl(arg_0: Value, arg_1: Value, arg_2: Value, arg_3: Value, arg_4: Value, arg_5: Value) -> Value {
    match arg_5 {
        Value::Inductive(n, idx, ctor_args) => {
            if n != "Eq" { panic!("rec_Eq: type mismatch, expected Eq got {}", n); }
            match idx {
                0 => { // refl
                    let mut curr_fn = arg_4.clone();
                    curr_fn
                }
                _ => panic!("rec_Eq: invalid constructor index {}", idx),
            }
        }
        _ => panic!("rec_Eq: expected Inductive value"),
    }
}

// Generic Recursor for Comp
// Layout: 1 params, 1 motive, 2 minors, 1 major = 5 total
fn rec_Comp_entry(arg_0: Value) -> Value {
    Value::Func(Rc::new(move |arg_1: Value| {
        let arg_0 = arg_0.clone();
    Value::Func(Rc::new(move |arg_2: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
    Value::Func(Rc::new(move |arg_3: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        let arg_2 = arg_2.clone();
    Value::Func(Rc::new(move |arg_4: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        let arg_2 = arg_2.clone();
        let arg_3 = arg_3.clone();
        rec_Comp_impl(arg_0, arg_1, arg_2, arg_3, arg_4)
    }))
    }))
    }))
    }))
}

fn rec_Comp_impl(arg_0: Value, arg_1: Value, arg_2: Value, arg_3: Value, arg_4: Value) -> Value {
    match arg_4 {
        Value::Inductive(n, idx, ctor_args) => {
            if n != "Comp" { panic!("rec_Comp: type mismatch, expected Comp got {}", n); }
            match idx {
                0 => { // ret
                    let mut curr_fn = arg_2.clone();
                    let val_0 = ctor_args[0].clone();
                    match curr_fn { Value::Func(f) => curr_fn = f(val_0.clone()), _ => panic!("rec_Comp: expected function for arg 0") }
                    curr_fn
                }
                1 => { // bind
                    let mut curr_fn = arg_3.clone();
                    let val_0 = ctor_args[0].clone();
                    match curr_fn { Value::Func(f) => curr_fn = f(val_0.clone()), _ => panic!("rec_Comp: expected function for arg 0") }
                    let val_1 = ctor_args[1].clone();
                    match curr_fn { Value::Func(f) => curr_fn = f(val_1.clone()), _ => panic!("rec_Comp: expected function for arg 1") }
                    // Compute IH for recursive arg 1
                    let ih_1 = rec_Comp_impl(arg_0.clone(), arg_1.clone(), arg_2.clone(), arg_3.clone(), val_1.clone());
                    match curr_fn { Value::Func(f) => curr_fn = f(ih_1), _ => panic!("rec_Comp: expected function for IH 1") }
                    let val_2 = ctor_args[2].clone();
                    match curr_fn { Value::Func(f) => curr_fn = f(val_2.clone()), _ => panic!("rec_Comp: expected function for arg 2") }
                    curr_fn
                }
                _ => panic!("rec_Comp: invalid constructor index {}", idx),
            }
        }
        _ => panic!("rec_Comp: expected Inductive value"),
    }
}

fn main() {
}
