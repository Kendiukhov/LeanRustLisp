// Q3 (Rust): "reverse is an involution".
//
// A compiler-checked proof of `reverse(reverse(v)) == v` for all `v` is not expressible in
// rustc: Rust's type system has no propositions or proof terms. Proving it needs an external
// verifier (e.g. Verus or Creusot), which this comparison deliberately does not install.
// The closest thing rustc itself can do is a run-time assertion over chosen inputs, below.
//
// Variants (rustc --cfg <name>):
//   (none)   correct reverse: compiles, the assertion holds on the tested inputs
//   buggy    a wrong reverse (drops the first element when the length is 3 or more):
//            still compiles; the bug is only found by the run-time assertion

fn reverse<T: Clone>(v: &[T]) -> Vec<T> {
    let out: Vec<T> = v.iter().rev().cloned().collect();
    #[cfg(buggy)]
    let out: Vec<T> = if v.len() >= 3 { out[..out.len() - 1].to_vec() } else { out };
    out
}

fn main() {
    let mut tested = 0;
    for n in 0..=8u32 {
        let v: Vec<u32> = (0..n).collect();
        assert_eq!(reverse(&reverse(&v)), v, "reverse is not an involution on {:?}", v);
        tested += 1;
    }
    println!("reverse(reverse(v)) == v held on {} tested inputs (run-time check only)", tested);
}
