#![no_main]

use libfuzzer_sys::fuzz_target;
use mir::analysis::nll::NllChecker;
use mir::types::{MirType, Mutability, Region};
use mir::{
    BasicBlock, BasicBlockData, Body, BorrowKind, CallOperand, Constant, Literal, Local, LocalDecl,
    Operand, Place, PlaceElem, Rvalue, Statement, SwitchTargets, Terminator,
};

const MAX_LOCALS: usize = 8;
const MAX_BLOCKS: usize = 6;
const MAX_STMTS: usize = 8;
const MAX_ARGS: usize = 3;

struct ByteCursor<'a> {
    data: &'a [u8],
    idx: usize,
}

impl<'a> ByteCursor<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, idx: 0 }
    }

    fn next_u8(&mut self) -> u8 {
        if self.idx >= self.data.len() {
            return 0;
        }
        let b = self.data[self.idx];
        self.idx += 1;
        b
    }

    fn next_u32(&mut self) -> u32 {
        let mut out = 0u32;
        for shift in 0..4 {
            out |= (self.next_u8() as u32) << (shift * 8);
        }
        out
    }

    fn gen_range(&mut self, max: usize) -> usize {
        if max == 0 {
            return 0;
        }
        (self.next_u32() as usize) % max
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u8() & 1) == 1
    }
}

fn random_scalar_type(cur: &mut ByteCursor<'_>) -> MirType {
    match cur.gen_range(3) {
        0 => MirType::Nat,
        1 => MirType::Bool,
        _ => MirType::Unit,
    }
}

fn random_type(cur: &mut ByteCursor<'_>, local_idx: usize) -> MirType {
    match cur.gen_range(4) {
        0 => MirType::Nat,
        1 => MirType::Bool,
        2 => MirType::Unit,
        _ => {
            let inner = random_scalar_type(cur);
            let mutability = if cur.gen_bool() {
                Mutability::Mut
            } else {
                Mutability::Not
            };
            MirType::Ref(Region(local_idx + 1), Box::new(inner), mutability)
        }
    }
}

fn random_local(cur: &mut ByteCursor<'_>, total_locals: usize) -> Local {
    Local(cur.gen_range(total_locals) as u32)
}

fn random_place(cur: &mut ByteCursor<'_>, total_locals: usize) -> Place {
    let local = random_local(cur, total_locals);
    let mut projection = Vec::new();
    if cur.gen_range(4) == 0 {
        projection.push(PlaceElem::Deref);
    }
    if cur.gen_range(10) == 0 {
        projection.push(PlaceElem::Deref);
    }
    Place { local, projection }
}

fn random_constant(cur: &mut ByteCursor<'_>) -> Constant {
    match cur.gen_range(3) {
        0 => Constant {
            literal: Literal::Unit,
            ty: MirType::Unit,
        },
        1 => Constant {
            literal: Literal::Bool(cur.gen_bool()),
            ty: MirType::Bool,
        },
        _ => Constant {
            literal: Literal::Nat(cur.next_u32() as u64),
            ty: MirType::Nat,
        },
    }
}

fn random_operand(cur: &mut ByteCursor<'_>, total_locals: usize) -> Operand {
    match cur.gen_range(3) {
        0 => Operand::Copy(random_place(cur, total_locals)),
        1 => Operand::Move(random_place(cur, total_locals)),
        _ => Operand::Constant(Box::new(random_constant(cur))),
    }
}

fn random_rvalue(cur: &mut ByteCursor<'_>, total_locals: usize) -> Rvalue {
    match cur.gen_range(3) {
        0 => Rvalue::Use(random_operand(cur, total_locals)),
        1 => Rvalue::Ref(
            if cur.gen_bool() {
                BorrowKind::Mut
            } else {
                BorrowKind::Shared
            },
            random_place(cur, total_locals),
        ),
        _ => Rvalue::Discriminant(random_place(cur, total_locals)),
    }
}

fn random_statement(cur: &mut ByteCursor<'_>, total_locals: usize) -> Statement {
    match cur.gen_range(6) {
        0 | 1 | 2 => Statement::Assign(
            random_place(cur, total_locals),
            random_rvalue(cur, total_locals),
        ),
        3 => Statement::StorageDead(random_local(cur, total_locals)),
        4 => Statement::StorageLive(random_local(cur, total_locals)),
        _ => Statement::Nop,
    }
}

fn random_call_operand(cur: &mut ByteCursor<'_>, total_locals: usize) -> CallOperand {
    if cur.gen_range(3) == 0 {
        CallOperand::Borrow(
            if cur.gen_bool() {
                BorrowKind::Mut
            } else {
                BorrowKind::Shared
            },
            random_place(cur, total_locals),
        )
    } else {
        CallOperand::Operand(random_operand(cur, total_locals))
    }
}

fn random_terminator(
    cur: &mut ByteCursor<'_>,
    block_count: usize,
    total_locals: usize,
) -> Terminator {
    match cur.gen_range(4) {
        0 => Terminator::Return,
        1 => Terminator::Goto {
            target: BasicBlock(cur.gen_range(block_count) as u32),
        },
        2 => {
            let target_count = 2 + cur.gen_range(2);
            let mut targets = Vec::with_capacity(target_count);
            for _ in 0..target_count {
                targets.push(BasicBlock(cur.gen_range(block_count) as u32));
            }
            let mut values = Vec::with_capacity(target_count.saturating_sub(1));
            for _ in 0..target_count.saturating_sub(1) {
                values.push(cur.next_u32() as u128);
            }
            Terminator::SwitchInt {
                discr: random_operand(cur, total_locals),
                targets: SwitchTargets { values, targets },
            }
        }
        _ => Terminator::Call {
            func: random_call_operand(cur, total_locals),
            args: (0..cur.gen_range(MAX_ARGS + 1))
                .map(|_| random_operand(cur, total_locals))
                .collect(),
            destination: random_place(cur, total_locals),
            target: if cur.gen_range(4) == 0 {
                None
            } else {
                Some(BasicBlock(cur.gen_range(block_count) as u32))
            },
        },
    }
}

fn build_body(cur: &mut ByteCursor<'_>) -> Body {
    let total_locals = 1 + cur.gen_range(MAX_LOCALS);
    let block_count = 1 + cur.gen_range(MAX_BLOCKS);

    let mut body = Body::new(0);
    for idx in 0..total_locals {
        let ty = random_type(cur, idx);
        body.local_decls.push(LocalDecl::new(ty, None));
    }

    for _ in 0..block_count {
        let stmt_count = cur.gen_range(MAX_STMTS);
        let mut statements = Vec::with_capacity(stmt_count);
        for _ in 0..stmt_count {
            statements.push(random_statement(cur, total_locals));
        }
        let terminator = Some(random_terminator(cur, block_count, total_locals));
        body.basic_blocks.push(BasicBlockData {
            statements,
            terminator,
        });
    }

    body
}

fuzz_target!(|data: &[u8]| {
    let mut cursor = ByteCursor::new(data);
    let body = build_body(&mut cursor);
    let mut checker = NllChecker::new(&body);
    checker.check();
});
