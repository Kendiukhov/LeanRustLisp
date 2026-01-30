
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
fn not() -> Value {
{ Value::Func(Rc::new(move |x_0: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_0 = x_0.clone(); Value::Func(Rc::new(move |x_1: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#false()), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#true()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_0.clone()), _ => panic!("Expected Func") }) })) }
}
fn if_nat() -> Value {
{ Value::Func(Rc::new(move |x_2: Value| { { let x_2 = x_2.clone(); Value::Func(Rc::new(move |x_3: Value| { { let x_2 = x_2.clone(); let x_3 = x_3.clone(); Value::Func(Rc::new(move |x_4: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_2 = x_2.clone(); let x_3 = x_3.clone(); let x_4 = x_4.clone(); Value::Func(Rc::new(move |x_5: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_3.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_4.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_2.clone()), _ => panic!("Expected Func") }) })) } })) } })) }
}
fn and() -> Value {
{ Value::Func(Rc::new(move |x_6: Value| { { let x_6 = x_6.clone(); Value::Func(Rc::new(move |x_7: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_6 = x_6.clone(); let x_7 = x_7.clone(); Value::Func(Rc::new(move |x_8: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_7.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#false()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_6.clone()), _ => panic!("Expected Func") }) })) } })) }
}
fn or() -> Value {
{ Value::Func(Rc::new(move |x_9: Value| { { let x_9 = x_9.clone(); Value::Func(Rc::new(move |x_10: Value| { (match (match (match (match Value::Func(Rc::new(rec_bool_entry)) { Value::Func(f) => f({ let x_9 = x_9.clone(); let x_10 = x_10.clone(); Value::Func(Rc::new(move |x_11: Value| { Value::Unit })) }), _ => panic!("Expected Func") }) { Value::Func(f) => f(r#true()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_10.clone()), _ => panic!("Expected Func") }) { Value::Func(f) => f(x_9.clone()), _ => panic!("Expected Func") }) })) } })) }
}
fn nil() -> Value {
Value::Func(Rc::new(|_| Value::List(Rc::new(List::Nil))))
}
fn cons() -> Value {
Value::Func(Rc::new(|_| Value::Func(Rc::new(|h| { let h=h.clone(); Value::Func(Rc::new(move |t| match t { Value::List(l) => Value::List(Rc::new(List::Cons(h.clone(), l))), _ => panic!("cons expects List") } )) } ))))
}
fn mkBox() -> Value {
Value::Func(Rc::new(move |arg_0: Value| { Value::Inductive("MyBox".to_string(), 0, vec![arg_0.clone()]) }))
}
fn myzero() -> Value {
Value::Inductive("MyNat".to_string(), 0, vec![])
}
fn mysucc() -> Value {
Value::Func(Rc::new(move |arg_0: Value| { Value::Inductive("MyNat".to_string(), 1, vec![arg_0.clone()]) }))
}
// Rec for MyBox
fn rec_MyBox_entry(arg_0: Value) -> Value {
    Value::Func(Rc::new(move |arg_1: Value| {
        let arg_0 = arg_0.clone();
    Value::Func(Rc::new(move |arg_2: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        rec_MyBox_impl(arg_0, arg_1, arg_2)
    }))
    }))
}

fn rec_MyBox_impl(arg_0: Value, arg_1: Value, arg_2: Value) -> Value {
    match arg_2 {
        Value::Inductive(n, idx, ctor_args) => {
            if n != "MyBox" { panic!("rec_MyBox mismatch"); }
            match idx {
                0 => {
                    // Apply minor premise 1
                    let mut curr_fn = arg_1.clone();
                    let val_0 = ctor_args[0].clone();
                    match curr_fn { Value::Func(f) => curr_fn = f(val_0.clone()), _ => panic!("arg app") }
                    curr_fn
                }
                _ => panic!("Invalid Ctor Index"),
            }
        }
        _ => panic!("Expected Inductive"),
    }
}

// Rec for MyNat
fn rec_MyNat_entry(arg_0: Value) -> Value {
    Value::Func(Rc::new(move |arg_1: Value| {
        let arg_0 = arg_0.clone();
    Value::Func(Rc::new(move |arg_2: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
    Value::Func(Rc::new(move |arg_3: Value| {
        let arg_0 = arg_0.clone();
        let arg_1 = arg_1.clone();
        let arg_2 = arg_2.clone();
        rec_MyNat_impl(arg_0, arg_1, arg_2, arg_3)
    }))
    }))
    }))
}

fn rec_MyNat_impl(arg_0: Value, arg_1: Value, arg_2: Value, arg_3: Value) -> Value {
    match arg_3 {
        Value::Inductive(n, idx, ctor_args) => {
            if n != "MyNat" { panic!("rec_MyNat mismatch"); }
            match idx {
                0 => {
                    // Apply minor premise 1
                    let mut curr_fn = arg_1.clone();
                    curr_fn
                }
                1 => {
                    // Apply minor premise 2
                    let mut curr_fn = arg_2.clone();
                    let val_0 = ctor_args[0].clone();
                    match curr_fn { Value::Func(f) => curr_fn = f(val_0.clone()), _ => panic!("arg app") }
                    let ih_0 = rec_MyNat_impl(arg_0.clone(), arg_1.clone(), arg_2.clone(), val_0.clone());
                    match curr_fn { Value::Func(f) => curr_fn = f(ih_0), _ => panic!("ih app") }
                    curr_fn
                }
                _ => panic!("Invalid Ctor Index"),
            }
        }
        _ => panic!("Expected Inductive"),
    }
}

fn main() {
}
