// Q1 (Rust, type-level naturals): a length-indexed vector whose `head` is total.
//
// The length index is a type-level Peano numeral (`Z`, `S<N>`). The representation of a
// vector is computed from its index by a generic associated type: `Vect<T, S<S<Z>>>` is
// stored as `(T, (T, ()))`. `head` is a field access with no runtime check, and it only
// accepts a vector whose index has the form `S<_>`.
//
// Variants (rustc --cfg <name>):
//   (none)  head of a 3-element vector: accepted, prints 1
//   empty   head of the empty vector: rejected (E0308, mismatched types)

use std::marker::PhantomData;

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

struct Vect<T, N: Nat>(N::Arr<T>);

fn nil<T>() -> Vect<T, Z> {
    Vect(())
}

fn cons<T, N: Nat>(x: T, v: Vect<T, N>) -> Vect<T, S<N>> {
    Vect((x, v.0))
}

fn head<T, N: Nat>(v: Vect<T, S<N>>) -> T {
    (v.0).0
}

fn main() {
    let v = cons(1u64, cons(2, cons(3, nil())));
    println!("head = {}", head(v));

    #[cfg(empty)]
    {
        let e = nil::<u64>();
        println!("head = {}", head(e));
    }
}
