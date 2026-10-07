// Q7 (Rust, const generics): the same protocol counter written with const generics.
//
// `Chan<N>` with `send: Chan<N> -> Chan<{N - 1}>` is the direct formulation. On stable Rust
// (1.78) the return type is rejected because `N - 1` is a const operation on a generic
// parameter (needs the unstable `generic_const_exprs`). Const generics can still pair a
// `[u64; N]` with a `Chan<N>` at the call site, but they cannot express the decrement, so
// the per-message state change cannot be typed. This file is a limit probe.

struct Chan<const N: usize> {
    sent: Vec<u64>,
}

impl<const N: usize> Chan<N> {
    fn send(mut self, x: u64) -> Chan<{ N - 1 }> {
        self.sent.push(x);
        Chan { sent: self.sent }
    }
}

impl Chan<0> {
    fn close(self) -> Vec<u64> {
        self.sent
    }
}

fn main() {
    let c: Chan<2> = Chan { sent: Vec::new() };
    println!("{:?}", c.send(1).send(2).close());
}
