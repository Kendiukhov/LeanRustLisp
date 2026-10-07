// Q4 (Rust): proof/ghost values are absent at run time.
//
// Rust has no proof terms, but the usual encoding of "evidence" is a zero-sized type:
// a token that can only be obtained from a checking function (`IsNonZero`), phantom
// type-level indices (`PhantomData<...>`), and type-level lengths (`Vect<T, N>` from
// q01/q02). All of them have size 0, so they occupy no memory and are not passed in
// registers. Run `rustc --emit=llvm-ir` on this file to see that `div_with_proof` takes
// only the two u64 arguments (the run script greps the `define` line). The program checks
// the sizes itself and exits with an error if any evidence value occupies memory.
//
// Variants (rustc --cfg <name>):
//   (none)            accepted; prints the sizes and the result of div_with_proof
//   forge             build the evidence directly, outside the module that owns it:
//                     rejected (E0423, cannot initialize a tuple struct with private fields)
//   zero_divisor      divide by 0 with evidence obtained from `check_nonzero(0)`: accepted; the
//                     evidence is a run-time check, so `check_nonzero(0)` returns None and the
//                     program stops at run time (the token is not tied to the value at the type level)
//   index_at_runtime  read the type-level length of a Vect as a run-time value: rejected
//                     (E0423, a type parameter is not a value); the length is only available
//                     at run time if it is computed through a trait, i.e. if the program asks for it

use std::marker::PhantomData;
use std::mem::size_of;

struct Z;
struct S<N>(PhantomData<N>);

trait Nat {
    type Arr<T>;
}
impl Nat for Z {
    type Arr<T> = ();
}
impl<N: Nat> Nat for S<N> {
    type Arr<T> = (T, N::Arr<T>);
}
struct Vect<T, N: Nat>(#[allow(dead_code)] N::Arr<T>);

#[cfg(index_at_runtime)]
fn length<T, N: Nat>(_v: &Vect<T, N>) -> usize {
    N
}

mod evidence {
    /// Evidence that a divisor is non-zero. The field is private to this module, so other
    /// modules can only get one from `check_nonzero`.
    #[derive(Clone, Copy)]
    pub struct IsNonZero(());

    pub fn check_nonzero(b: u64) -> Option<IsNonZero> {
        if b != 0 {
            Some(IsNonZero(()))
        } else {
            None
        }
    }

    #[no_mangle]
    #[inline(never)]
    pub fn div_with_proof(a: u64, b: u64, _evidence: IsNonZero) -> u64 {
        a / b
    }
}

use evidence::{check_nonzero, div_with_proof, IsNonZero};

fn main() {
    println!("size_of::<IsNonZero>() = {}", size_of::<IsNonZero>());
    println!("size_of::<PhantomData<S<S<Z>>>>() = {}", size_of::<PhantomData<S<S<Z>>>>());
    println!("size_of::<S<S<S<Z>>>>() = {}", size_of::<S<S<S<Z>>>>());
    println!(
        "size_of::<Vect<u64, S<S<S<Z>>>>>() = {} (= 3 * size_of::<u64>() = {}; no length stored)",
        size_of::<Vect<u64, S<S<S<Z>>>>>(),
        3 * size_of::<u64>()
    );
    assert_eq!(size_of::<IsNonZero>(), 0, "the evidence token occupies memory");
    assert_eq!(size_of::<Vect<u64, S<S<S<Z>>>>>(), 3 * size_of::<u64>(), "the index is stored");
    let p = check_nonzero(4).expect("4 is non-zero");
    println!("div_with_proof(12, 4, p) = {}", div_with_proof(12, 4, p));

    #[cfg(forge)]
    println!("{}", div_with_proof(1, 0, IsNonZero(())));

    #[cfg(zero_divisor)]
    {
        let z = check_nonzero(0).expect("no evidence that 0 is non-zero");
        println!("{}", div_with_proof(1, 0, z));
    }

    #[cfg(index_at_runtime)]
    {
        let v: Vect<u64, S<Z>> = Vect((7, ()));
        println!("length = {}", length(&v));
    }
}
