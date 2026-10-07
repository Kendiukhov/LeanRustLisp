//! Plain-Rust reference point for the vec_rev_sum workload (context only; see bench/README.md).
//!
//! Usage: vec_rev_sum <inplace|snoc> <n>
//!   inplace: a Vec<u64> of n ones, reversed in place with `reverse()`, then summed.
//!   snoc:    the algorithm of the case study's `vreverse`: reverse(h :: t) = snoc(reverse(t), h),
//!            where every snoc builds a new vector (copy of its input plus one element).
//! Prints `Result: <sum>` (the sum is n). Built with `rustc -O`.
use std::hint::black_box;

fn snoc(v: &[u64], x: u64) -> Vec<u64> {
    let mut w = Vec::with_capacity(v.len() + 1);
    w.extend_from_slice(v);
    w.push(x);
    w
}

/// reverse(v) for v = [h1, ..., hn]: snoc(reverse([h2, ..., hn]), h1), evaluated from the end.
fn reverse_by_snoc(v: &[u64]) -> Vec<u64> {
    let mut acc: Vec<u64> = Vec::new();
    for &h in v.iter().rev() {
        acc = snoc(&acc, h);
    }
    acc
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str).unwrap_or("inplace");
    let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1000);
    let v: Vec<u64> = black_box(vec![1u64; n]);
    let sum: u64 = match mode {
        "inplace" => {
            let mut w = v;
            w.reverse();
            black_box(&mut w);
            w.iter().sum()
        }
        "snoc" => {
            let w = reverse_by_snoc(&v);
            black_box(&w);
            w.iter().sum()
        }
        other => panic!("unknown mode {}", other),
    };
    println!("Result: {}", black_box(sum));
}
