// Q2 (Rust, type-level naturals): `append` whose result length is the sum of the input lengths.
//
// Type-level addition is a trait with an associated type `Sum`, defined by recursion on
// the first argument; `append` is implemented by the same recursion, so its body is
// checked against the type `Vect<T, N + M>` (written `Vect<T, <N as Add<M>>::Sum>`).
//
// Variants (rustc --cfg <name>):
//   (none)       append a 2-vector and a 1-vector into a 3-vector: accepted, prints [1, 2, 3]
//   wrong_len    annotate the result of the same append as a 2-vector: rejected (E0308)
//   drop_elem    an `append` implementation that forgets the head element: rejected (E0308)

use std::marker::PhantomData;

struct Z;
struct S<N>(PhantomData<N>);

trait Nat {
    type Arr<T>;
    fn to_vec<T>(a: Self::Arr<T>, out: &mut Vec<T>);
}
impl Nat for Z {
    type Arr<T> = ();
    fn to_vec<T>(_a: (), _out: &mut Vec<T>) {}
}
impl<N: Nat> Nat for S<N> {
    type Arr<T> = (T, N::Arr<T>);
    fn to_vec<T>(a: (T, N::Arr<T>), out: &mut Vec<T>) {
        out.push(a.0);
        N::to_vec(a.1, out);
    }
}

struct Vect<T, N: Nat>(N::Arr<T>);

fn nil<T>() -> Vect<T, Z> {
    Vect(())
}
fn cons<T, N: Nat>(x: T, v: Vect<T, N>) -> Vect<T, S<N>> {
    Vect((x, v.0))
}
fn to_vec<T, N: Nat>(v: Vect<T, N>) -> Vec<T> {
    let mut out = Vec::new();
    N::to_vec(v.0, &mut out);
    out
}

// Type-level addition, with the matching value-level append.
trait Add<M: Nat>: Nat {
    type Sum: Nat;
    fn app<T>(a: Self::Arr<T>, b: M::Arr<T>) -> <Self::Sum as Nat>::Arr<T>;
}
impl<M: Nat> Add<M> for Z {
    type Sum = M; // 0 + m = m
    fn app<T>(_a: (), b: M::Arr<T>) -> M::Arr<T> {
        b
    }
}
impl<M: Nat, N: Add<M>> Add<M> for S<N> {
    type Sum = S<N::Sum>; // (n + 1) + m = (n + m) + 1
    #[cfg(not(drop_elem))]
    fn app<T>(a: (T, N::Arr<T>), b: M::Arr<T>) -> (T, <N::Sum as Nat>::Arr<T>) {
        (a.0, N::app(a.1, b))
    }
    #[cfg(drop_elem)]
    fn app<T>(a: (T, N::Arr<T>), b: M::Arr<T>) -> (T, <N::Sum as Nat>::Arr<T>) {
        N::app(a.1, b)
    }
}

fn append<T, N: Add<M>, M: Nat>(a: Vect<T, N>, b: Vect<T, M>) -> Vect<T, N::Sum> {
    Vect(N::app(a.0, b.0))
}

fn main() {
    let two = cons(1u64, cons(2, nil()));
    let one = cons(3u64, nil());

    #[cfg(not(wrong_len))]
    let r: Vect<u64, S<S<S<Z>>>> = append(two, one);
    #[cfg(wrong_len)]
    let r: Vect<u64, S<S<Z>>> = append(two, one);

    println!("{:?}", to_vec(r));
}
