use mir::analysis::liveness::compute_liveness;
use mir::analysis::liveness::LivenessResult;
use mir::types::MirType;
use mir::{
    BasicBlock, BasicBlockData, Body, BorrowKind, CallOperand, Constant, Literal, Local, LocalDecl,
    Operand, Place, RuntimeCheckKind, Rvalue, Statement, SwitchTargets, Terminator,
};
use std::collections::HashSet;
use std::time::Instant;

fn synthetic_body(num_blocks: usize, statements_per_block: usize, num_locals: usize) -> Body {
    assert!(
        num_blocks > 1,
        "synthetic body requires at least two blocks"
    );
    assert!(
        num_locals > 3,
        "synthetic body requires at least four locals"
    );

    let mut body = Body::new(0);
    for idx in 0..num_locals {
        let name = if idx == 0 {
            Some("_return".to_string())
        } else {
            None
        };
        body.local_decls.push(LocalDecl::new(MirType::Nat, name));
    }

    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    for block_idx in 0..num_blocks {
        let mut statements = Vec::with_capacity(statements_per_block);
        for stmt_idx in 0..statements_per_block {
            seed = lcg(seed);
            let key = seed ^ ((block_idx as u64) << 17) ^ ((stmt_idx as u64) << 9);
            let local = Local((key % num_locals as u64) as u32);
            let aux = Local(((key >> 12) % num_locals as u64) as u32);
            let aux2 = Local(((key >> 28) % num_locals as u64) as u32);
            let nat = Operand::Constant(Box::new(Constant {
                literal: Literal::Nat((key & 31) + 1),
                ty: MirType::Nat,
            }));
            let stmt = match key % 6 {
                0 => Statement::Assign(
                    Place::from(local),
                    Rvalue::Use(Operand::Copy(Place::from(aux))),
                ),
                1 => Statement::Assign(
                    Place::from(local),
                    Rvalue::Ref(
                        if key & 1 == 0 {
                            BorrowKind::Shared
                        } else {
                            BorrowKind::Mut
                        },
                        Place::from(aux),
                    ),
                ),
                2 => Statement::Assign(Place::from(local), Rvalue::Use(nat)),
                3 => Statement::RuntimeCheck(RuntimeCheckKind::BoundsCheck {
                    local: aux,
                    index: aux2,
                }),
                4 => Statement::StorageLive(local),
                _ => Statement::StorageDead(local),
            };
            statements.push(stmt);
        }

        let terminator = if block_idx + 1 == num_blocks {
            Terminator::Return
        } else if block_idx % 5 == 0 && block_idx + 2 < num_blocks {
            Terminator::SwitchInt {
                discr: Operand::Copy(Place::from(Local(((block_idx + 1) % num_locals) as u32))),
                targets: SwitchTargets {
                    values: vec![0],
                    targets: vec![
                        BasicBlock((block_idx + 1) as u32),
                        BasicBlock((block_idx + 2) as u32),
                    ],
                },
            }
        } else if block_idx % 7 == 0 {
            let destination = Place::from(Local(((block_idx + 3) % num_locals) as u32));
            Terminator::Call {
                func: CallOperand::Borrow(
                    BorrowKind::Shared,
                    Place::from(Local(((block_idx + 2) % num_locals) as u32)),
                ),
                args: vec![
                    Operand::Copy(Place::from(Local(((block_idx + 1) % num_locals) as u32))),
                    Operand::Copy(Place::from(Local(((block_idx + 4) % num_locals) as u32))),
                ],
                destination,
                target: Some(BasicBlock((block_idx + 1) as u32)),
            }
        } else {
            Terminator::Goto {
                target: BasicBlock((block_idx + 1) as u32),
            }
        };

        body.basic_blocks.push(BasicBlockData {
            statements,
            terminator: Some(terminator),
        });
    }

    body
}

fn lcg(x: u64) -> u64 {
    x.wrapping_mul(6364136223846793005).wrapping_add(1)
}

fn compute_liveness_reference(body: &Body) -> (Vec<HashSet<Local>>, Vec<HashSet<Local>>) {
    let mut ins = vec![HashSet::new(); body.basic_blocks.len()];
    let mut outs = vec![HashSet::new(); body.basic_blocks.len()];

    let mut changed = true;
    while changed {
        changed = false;
        for i in (0..body.basic_blocks.len()).rev() {
            let block = &body.basic_blocks[i];
            let mut new_out = HashSet::new();
            if let Some(term) = &block.terminator {
                for succ in successors(term) {
                    if let Some(succ_in) = ins.get(succ.index()) {
                        new_out.extend(succ_in.iter().copied());
                    }
                }
            }
            if new_out != outs[i] {
                outs[i] = new_out.clone();
                changed = true;
            }

            let mut current_live = new_out;
            if let Some(term) = &block.terminator {
                process_terminator_reference(term, &mut current_live);
            }
            for stmt in block.statements.iter().rev() {
                process_statement_reference(stmt, &mut current_live);
            }
            if current_live != ins[i] {
                ins[i] = current_live;
                changed = true;
            }
        }
    }

    (ins, outs)
}

fn successors(term: &Terminator) -> Vec<BasicBlock> {
    match term {
        Terminator::Goto { target } => vec![*target],
        Terminator::SwitchInt { targets, .. } => targets.targets.clone(),
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        _ => Vec::new(),
    }
}

fn process_statement_reference(stmt: &Statement, live: &mut HashSet<Local>) {
    match stmt {
        Statement::Assign(place, rvalue) => {
            if place.projection.is_empty() {
                live.remove(&place.local);
            } else {
                live.insert(place.local);
            }

            match rvalue {
                Rvalue::Use(op) => process_operand_reference(op, live),
                Rvalue::Ref(_, place) | Rvalue::Discriminant(place) => {
                    live.insert(place.local);
                }
            }
        }
        Statement::RuntimeCheck(check) => match check {
            RuntimeCheckKind::RefCellBorrow { local } => {
                live.insert(*local);
            }
            RuntimeCheckKind::MutexLock { local } => {
                live.insert(*local);
            }
            RuntimeCheckKind::BoundsCheck { local, index } => {
                live.insert(*local);
                live.insert(*index);
            }
        },
        Statement::StorageLive(local) | Statement::StorageDead(local) => {
            live.remove(local);
        }
        Statement::Nop => {}
    }
}

fn process_terminator_reference(term: &Terminator, live: &mut HashSet<Local>) {
    match term {
        Terminator::SwitchInt { discr, .. } => process_operand_reference(discr, live),
        Terminator::Call {
            func,
            args,
            destination,
            ..
        } => {
            process_call_operand_reference(func, live);
            for arg in args {
                process_operand_reference(arg, live);
            }
            if destination.projection.is_empty() {
                live.remove(&destination.local);
            } else {
                live.insert(destination.local);
            }
        }
        Terminator::Return => {
            live.insert(Local(0));
        }
        _ => {}
    }
}

fn process_operand_reference(op: &Operand, live: &mut HashSet<Local>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            live.insert(place.local);
        }
        Operand::Constant(c) => {
            if let Some(captures) = c.literal.capture_operands() {
                for capture in captures {
                    process_operand_reference(capture, live);
                }
            }
        }
    }
}

fn process_call_operand_reference(op: &CallOperand, live: &mut HashSet<Local>) {
    match op {
        CallOperand::Borrow(_, place) => {
            live.insert(place.local);
        }
        CallOperand::Operand(op) => process_operand_reference(op, live),
    }
}

fn fingerprint(result: &LivenessResult) -> u64 {
    const OFFSET: u64 = 1469598103934665603;
    const PRIME: u64 = 1099511628211;

    let mut hash = OFFSET;
    for set in result.ins.iter().chain(result.outs.iter()) {
        hash ^= 0xFF;
        hash = hash.wrapping_mul(PRIME);
        for local in set.iter() {
            hash ^= local.0 as u64 + 1;
            hash = hash.wrapping_mul(PRIME);
        }
    }
    hash
}

#[test]
fn liveness_regression_matches_hashset_reference() {
    let body = synthetic_body(32, 10, 48);
    let computed = compute_liveness(&body);
    let (ref_ins, ref_outs) = compute_liveness_reference(&body);

    for block_idx in 0..body.basic_blocks.len() {
        let actual_in: HashSet<Local> = computed.ins[block_idx].iter().collect();
        let actual_out: HashSet<Local> = computed.outs[block_idx].iter().collect();
        assert_eq!(
            actual_in, ref_ins[block_idx],
            "block {block_idx} entry liveness diverged from reference"
        );
        assert_eq!(
            actual_out, ref_outs[block_idx],
            "block {block_idx} exit liveness diverged from reference"
        );
    }
}

#[test]
fn liveness_stability_is_deterministic_across_runs() {
    let body = synthetic_body(40, 8, 64);
    let baseline = compute_liveness(&body);
    let baseline_hash = fingerprint(&baseline);

    for _ in 0..32 {
        let current = compute_liveness(&body);
        assert_eq!(
            fingerprint(&current),
            baseline_hash,
            "repeated liveness runs must remain bit-for-bit stable"
        );
    }
}

#[test]
fn liveness_microbench_bitset_not_pathologically_slower_than_reference() {
    let body = synthetic_body(96, 12, 160);
    let iterations = 19usize;

    let mut bitset_digest = 0u64;
    let bitset_start = Instant::now();
    for _ in 0..iterations {
        bitset_digest ^= fingerprint(&compute_liveness(&body));
    }
    let bitset_elapsed = bitset_start.elapsed();

    let mut reference_digest = 0u64;
    let reference_start = Instant::now();
    for _ in 0..iterations {
        let (ins, outs) = compute_liveness_reference(&body);
        // Stable digest from reference sets by scanning locals in numeric order.
        let mut hash = 1469598103934665603u64;
        for set in ins.iter().chain(outs.iter()) {
            for local_idx in 0..body.local_decls.len() {
                if set.contains(&Local(local_idx as u32)) {
                    hash ^= local_idx as u64 + 1;
                    hash = hash.wrapping_mul(1099511628211);
                }
            }
        }
        reference_digest ^= hash;
    }
    let reference_elapsed = reference_start.elapsed();

    assert_ne!(
        bitset_digest, 0,
        "bitset microbench digest should not be zero"
    );
    assert_ne!(
        reference_digest, 0,
        "reference microbench digest should not be zero"
    );

    let bitset_ns = bitset_elapsed.as_nanos();
    let reference_ns = reference_elapsed.as_nanos();
    assert!(
        bitset_ns <= reference_ns * 5,
        "bitset liveness should stay within a sane performance envelope (bitset={}ns reference={}ns)",
        bitset_ns,
        reference_ns
    );
}
