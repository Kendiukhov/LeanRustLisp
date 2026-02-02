//! Stable pretty-printer for MIR, used for golden snapshot tests.
//!
//! This module produces deterministic, human-readable output that can be
//! compared against expected snapshots.

use crate::{Body, Statement, Terminator, Place, PlaceElem, RuntimeCheckKind,
            Rvalue, Operand, Constant, Literal, BorrowKind, Local};
use crate::types::{MirType, Mutability, IMKind, AdtId};
use std::fmt::Write;

/// Pretty-print a MIR body to a stable string representation.
pub fn pretty_print_body(body: &Body) -> String {
    let mut out = String::new();

    // Header
    writeln!(out, "fn (arg_count: {}) {{", body.arg_count).unwrap();

    // Local declarations
    writeln!(out, "    // Locals:").unwrap();
    for (i, decl) in body.local_decls.iter().enumerate() {
        let name = decl.name.as_deref().unwrap_or("_");
        let copy_marker = if decl.is_copy { " [copy]" } else { "" };
        let prop_marker = if decl.is_prop { " [prop]" } else { "" };
        writeln!(out, "    //   _{}: {} ({}){}{}",
            i, pretty_type(&decl.ty), name, copy_marker, prop_marker).unwrap();
    }
    writeln!(out).unwrap();

    // Basic blocks
    for (i, bb) in body.basic_blocks.iter().enumerate() {
        writeln!(out, "    bb{}: {{", i).unwrap();

        // Statements
        for stmt in &bb.statements {
            writeln!(out, "        {};", pretty_statement(stmt)).unwrap();
        }

        // Terminator
        if let Some(term) = &bb.terminator {
            writeln!(out, "        {}", pretty_terminator(term)).unwrap();
        }

        writeln!(out, "    }}").unwrap();
        writeln!(out).unwrap();
    }

    writeln!(out, "}}").unwrap();
    out
}

fn pretty_type(ty: &MirType) -> String {
    match ty {
        MirType::Unit => "()".to_string(),
        MirType::Bool => "Bool".to_string(),
        MirType::Nat => "Nat".to_string(),
        MirType::Adt(AdtId(name), args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let args_str: Vec<_> = args.iter().map(pretty_type).collect();
                format!("{}<{}>", name, args_str.join(", "))
            }
        }
        MirType::Ref(region, inner, mutability) => {
            let mut_str = match mutability {
                Mutability::Not => "",
                Mutability::Mut => "mut ",
            };
            format!("&'{} {}{}", region.0, mut_str, pretty_type(inner))
        }
        MirType::Fn(args, ret) => {
            let args_str: Vec<_> = args.iter().map(pretty_type).collect();
            format!("fn({}) -> {}", args_str.join(", "), pretty_type(ret))
        }
        MirType::RawPtr(inner, mutability) => {
            let mut_str = match mutability {
                Mutability::Not => "const",
                Mutability::Mut => "mut",
            };
            format!("*{} {}", mut_str, pretty_type(inner))
        }
        MirType::InteriorMutable(inner, kind) => {
            let kind_str = match kind {
                IMKind::RefCell => "RefCell",
                IMKind::Mutex => "Mutex",
                IMKind::Atomic => "Atomic",
            };
            format!("{}<{}>", kind_str, pretty_type(inner))
        }
    }
}

fn pretty_statement(stmt: &Statement) -> String {
    match stmt {
        Statement::Assign(place, rvalue) => {
            format!("{} = {}", pretty_place(place), pretty_rvalue(rvalue))
        }
        Statement::RuntimeCheck(check) => pretty_runtime_check(check),
        Statement::StorageLive(local) => format!("StorageLive({})", pretty_local(local)),
        Statement::StorageDead(local) => format!("StorageDead({})", pretty_local(local)),
        Statement::Nop => "nop".to_string(),
    }
}

fn pretty_runtime_check(check: &RuntimeCheckKind) -> String {
    match check {
        RuntimeCheckKind::RefCellBorrow { local } => {
            format!("RuntimeCheck::RefCellBorrow({})", pretty_local(local))
        }
        RuntimeCheckKind::MutexLock { local } => {
            format!("RuntimeCheck::MutexLock({})", pretty_local(local))
        }
        RuntimeCheckKind::BoundsCheck { local, index } => {
            format!(
                "RuntimeCheck::BoundsCheck({}, {})",
                pretty_local(local),
                pretty_local(index)
            )
        }
    }
}

fn pretty_terminator(term: &Terminator) -> String {
    match term {
        Terminator::Return => "return".to_string(),
        Terminator::Goto { target } => format!("goto -> bb{}", target.0),
        Terminator::SwitchInt { discr, targets } => {
            let mut s = format!("switchInt({}) -> [", pretty_operand(discr));
            for (i, (val, target)) in targets.values.iter().zip(targets.targets.iter()).enumerate() {
                if i > 0 { s.push_str(", "); }
                s.push_str(&format!("{}: bb{}", val, target.0));
            }
            // The last target is the "otherwise" case
            if targets.targets.len() > targets.values.len() {
                if !targets.values.is_empty() { s.push_str(", "); }
                s.push_str(&format!("otherwise: bb{}", targets.targets.last().unwrap().0));
            }
            s.push(']');
            s
        }
        Terminator::Call { func, args, destination, target } => {
            let args_str: Vec<_> = args.iter().map(pretty_operand).collect();
            let target_str = match target {
                Some(t) => format!(" -> bb{}", t.0),
                None => " -> !".to_string(),
            };
            format!("{} = {}({}){}",
                pretty_place(destination),
                pretty_operand(func),
                args_str.join(", "),
                target_str)
        }
        Terminator::Unreachable => "unreachable".to_string(),
    }
}

fn pretty_place(place: &Place) -> String {
    let mut s = pretty_local(&place.local);
    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => s = format!("(*{})", s),
            PlaceElem::Field(i) => s = format!("{}.{}", s, i),
            PlaceElem::Downcast(i) => s = format!("({} as variant#{})", s, i),
        }
    }
    s
}

fn pretty_local(local: &Local) -> String {
    format!("_{}", local.0)
}

fn pretty_rvalue(rvalue: &Rvalue) -> String {
    match rvalue {
        Rvalue::Use(op) => pretty_operand(op),
        Rvalue::Ref(kind, place) => {
            let kind_str = match kind {
                BorrowKind::Shared => "&",
                BorrowKind::Mut => "&mut ",
            };
            format!("{}{}", kind_str, pretty_place(place))
        }
        Rvalue::Discriminant(place) => format!("discriminant({})", pretty_place(place)),
    }
}

fn pretty_operand(op: &Operand) -> String {
    match op {
        Operand::Copy(place) => format!("copy {}", pretty_place(place)),
        Operand::Move(place) => format!("move {}", pretty_place(place)),
        Operand::Constant(c) => pretty_constant(c),
    }
}

fn pretty_constant(c: &Constant) -> String {
    match &c.literal {
        Literal::Unit => "()".to_string(),
        Literal::Nat(n) => format!("{}_nat", n),
        Literal::Bool(b) => format!("{}", b),
        Literal::Term(_) => "<term>".to_string(),
        Literal::Closure(idx, captures) => {
            let caps: Vec<_> = captures.iter().map(pretty_operand).collect();
            format!("closure#{}[{}]", idx, caps.join(", "))
        }
        Literal::Fix(idx, captures) => {
            let caps: Vec<_> = captures.iter().map(pretty_operand).collect();
            format!("fix#{}[{}]", idx, caps.join(", "))
        }
        Literal::InductiveCtor(name, idx, arity) => {
            format!("{}#{}(arity={})", name, idx, arity)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
    use crate::types::{Region, Mutability};

    #[test]
    fn test_pretty_simple_body() {
        let mut body = Body::new(1);
        body.local_decls.push(LocalDecl::new(MirType::Nat, Some("result".to_string())));
        body.local_decls.push(LocalDecl::new(MirType::Nat, Some("x".to_string())));

        body.basic_blocks.push(BasicBlockData {
            statements: vec![
                Statement::Assign(
                    Place::from(Local(0)),
                    Rvalue::Use(Operand::Copy(Place::from(Local(1))))
                )
            ],
            terminator: Some(Terminator::Return),
        });

        let output = pretty_print_body(&body);
        assert!(output.contains("fn (arg_count: 1)"));
        assert!(output.contains("_0: Nat (result)"));
        assert!(output.contains("_1: Nat (x)"));
        assert!(output.contains("_0 = copy _1"));
        assert!(output.contains("return"));
    }

    #[test]
    fn test_pretty_ref_types() {
        let ty = MirType::Ref(Region(1), Box::new(MirType::Nat), Mutability::Mut);
        assert_eq!(pretty_type(&ty), "&'1 mut Nat");

        let ty = MirType::Ref(Region(0), Box::new(MirType::Bool), Mutability::Not);
        assert_eq!(pretty_type(&ty), "&'0 Bool");
    }

    #[test]
    fn test_pretty_interior_mutable() {
        let ty = MirType::InteriorMutable(Box::new(MirType::Nat), IMKind::RefCell);
        assert_eq!(pretty_type(&ty), "RefCell<Nat>");

        let ty = MirType::InteriorMutable(Box::new(MirType::Bool), IMKind::Mutex);
        assert_eq!(pretty_type(&ty), "Mutex<Bool>");
    }

    #[test]
    fn test_pretty_switch() {
        let term = Terminator::SwitchInt {
            discr: Operand::Copy(Place::from(Local(1))),
            targets: SwitchTargets {
                values: vec![0, 1],
                targets: vec![BasicBlock(1), BasicBlock(2), BasicBlock(3)],
            },
        };
        let output = pretty_terminator(&term);
        assert!(output.contains("switchInt(copy _1)"));
        assert!(output.contains("0: bb1"));
        assert!(output.contains("1: bb2"));
        assert!(output.contains("otherwise: bb3"));
    }
}
