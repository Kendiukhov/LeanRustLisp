// Q7 (Rust, type-level naturals): the protocol length is tied to the data length.
//
// `Chan<N>` is a channel in the state "N messages remaining" (N a type-level Peano numeral).
// `send` exists only on `Chan<S<N>>` and returns `Chan<N>`; `close` exists only on `Chan<Z>`.
// `send_vec` sends every element of a length-indexed vector `Vect<u64, N>` over a `Chan<N>`
// and then closes it. It is generic in N: the recursion over N is a trait implemented for
// `Z` and for `S<N>`, and each implementation is type-checked once, for all N.
// (Stable const generics cannot express this; see q07_protocol_const_generics.rs.)
//
// Variants (rustc --cfg <name>):
//   (none)        send a 3-vector over a Chan<3>, then a manual send/send/close on a Chan<2>: accepted
//   too_many      a third send on a Chan<2>: rejected (E0599, no method `send` on Chan<Z>)
//   too_few       close a Chan<2> after one send: rejected (E0599, no method `close` on Chan<S<Z>>)
//   len_mismatch  send_vec with a 3-vector and a Chan<2>: rejected (E0308)
//   skip_send     a send_all step that forgets to send: rejected (E0308)
//   abandon       drop a Chan<1> without sending or closing: ACCEPTED (Rust is affine, not
//                 linear: a value may always be dropped)

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

/// A channel with N messages remaining. Not Copy/Clone: every operation consumes it.
struct Chan<N> {
    sent: Vec<u64>,
    _remaining: PhantomData<N>,
}

fn open<N>() -> Chan<N> {
    Chan { sent: Vec::new(), _remaining: PhantomData }
}

impl<N> Chan<S<N>> {
    fn send(mut self, x: u64) -> Chan<N> {
        self.sent.push(x);
        Chan { sent: self.sent, _remaining: PhantomData }
    }
}

impl Chan<Z> {
    fn close(self) -> Vec<u64> {
        self.sent
    }
}

trait SendAll: Nat + Sized {
    fn send_all(v: Self::Arr<u64>, c: Chan<Self>) -> Vec<u64>;
}
impl SendAll for Z {
    fn send_all(_v: (), c: Chan<Z>) -> Vec<u64> {
        c.close()
    }
}
impl<N: SendAll> SendAll for S<N> {
    #[cfg(not(skip_send))]
    fn send_all(v: (u64, N::Arr<u64>), c: Chan<S<N>>) -> Vec<u64> {
        N::send_all(v.1, c.send(v.0))
    }
    #[cfg(skip_send)]
    fn send_all(v: (u64, N::Arr<u64>), c: Chan<S<N>>) -> Vec<u64> {
        N::send_all(v.1, c)
    }
}

fn send_vec<N: SendAll>(v: Vect<u64, N>, c: Chan<N>) -> Vec<u64> {
    N::send_all(v.0, c)
}

fn main() {
    let v = cons(10, cons(20, cons(30, nil())));
    #[cfg(not(len_mismatch))]
    let c: Chan<S<S<S<Z>>>> = open();
    #[cfg(len_mismatch)]
    let c: Chan<S<S<Z>>> = open();
    println!("send_vec transcript: {:?}", send_vec(v, c));

    let c2: Chan<S<S<Z>>> = open();
    #[cfg(not(any(too_many, too_few)))]
    let t = c2.send(1).send(2).close();
    #[cfg(too_many)]
    let t = c2.send(1).send(2).send(3).close();
    #[cfg(too_few)]
    let t = c2.send(1).close();
    println!("manual transcript: {:?}", t);

    #[cfg(abandon)]
    {
        let c3: Chan<S<Z>> = open();
        drop(c3);
        println!("a Chan<S<Z>> was dropped without sending or closing");
    }
}
