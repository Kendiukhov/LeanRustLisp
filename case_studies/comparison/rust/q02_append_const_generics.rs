// Q2 (Rust, const generics): `append` whose result length is the sum of the input lengths.
//
// This is the direct statement of the property with const generics. Stable Rust (1.78)
// rejects it: the return type `[T; N + M]` uses generic parameters in a const expression,
// which requires the unstable `generic_const_exprs` feature. This file is a limit probe;
// the expected outcome on stable is a compile-time rejection of the *signature*.

fn append<T: Copy + Default, const N: usize, const M: usize>(a: [T; N], b: [T; M]) -> [T; N + M] {
    let mut out = [T::default(); N + M];
    out[..N].copy_from_slice(&a);
    out[N..].copy_from_slice(&b);
    out
}

fn main() {
    let r = append([1u64, 2], [3u64]);
    println!("{:?}", r);
}
