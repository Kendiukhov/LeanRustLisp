// Q1 (Rust, const generics): a `head` on fixed-length arrays `[T; N]` that is rejected
// for N = 0 at compile time.
//
// Stable Rust cannot write the type `[T; N + 1]` for a generic `N` (that needs the
// unstable `generic_const_exprs` feature; variant `succ_type` below). The closest
// stable encoding is an associated-const assertion. It is evaluated when `head::<T, N>`
// is instantiated (a post-monomorphization error), so it fires during a full build but
// not during a check-only build (`rustc --emit=metadata`, i.e. `cargo check`).
//
// Variants (rustc --cfg <name>):
//   (none)       head of a 3-element array: accepted, prints 10
//   empty        head of a 0-element array: rejected when the instance is built (E0080)
//   plain_empty  the same call through `head_plain`, which has no assertion: accepted,
//                then panics at run time (index out of bounds)
//   succ_type    the direct formulation `fn head_succ(v: &[T; N + 1]) -> T`: rejected on
//                stable ("generic parameters may not be used in const operations")

struct NonEmpty<const N: usize>;

impl<const N: usize> NonEmpty<N> {
    const OK: () = assert!(N > 0, "head of an empty array");
}

fn head<T: Copy, const N: usize>(v: &[T; N]) -> T {
    #[allow(clippy::let_unit_value)]
    let () = NonEmpty::<N>::OK; // evaluated per instance, at compile time
    v[0]
}

#[cfg(succ_type)]
fn head_succ<T: Copy, const N: usize>(v: &[T; N + 1]) -> T {
    v[0]
}

#[allow(dead_code)]
fn head_plain<T: Copy, const N: usize>(v: &[T; N]) -> T {
    v[0]
}

fn main() {
    let a = [10u64, 20, 30];
    println!("head = {}", head(&a));

    #[cfg(empty)]
    {
        let e: [u64; 0] = [];
        println!("head = {}", head(&e));
    }

    #[cfg(plain_empty)]
    {
        let e: [u64; 0] = [];
        println!("head_plain = {}", head_plain(&e));
    }
}
