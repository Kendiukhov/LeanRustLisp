// Q6 (Rust): calling an operation in the wrong protocol state is a compile-time error.
//
// Typestate encoding: the state is a phantom type parameter, each operation consumes the
// channel in one state and returns it in the next, and an operation exists only in the
// `impl` block of the states where it is allowed.
//
// Variants (rustc --cfg <name>):
//   (none)            send, send, close: accepted
//   send_after_close  send on a closed channel: rejected (E0599, no method `send` on Chan<Closed>)
//   close_twice       close a closed channel: rejected (E0599, no method `close` on Chan<Closed>)

use std::marker::PhantomData;

struct Open;
struct Closed;

struct Chan<State> {
    log: Vec<u64>,
    _state: PhantomData<State>,
}

impl Chan<Open> {
    fn new() -> Self {
        Chan { log: Vec::new(), _state: PhantomData }
    }
    fn send(mut self, x: u64) -> Chan<Open> {
        self.log.push(x);
        self
    }
    fn close(self) -> Chan<Closed> {
        Chan { log: self.log, _state: PhantomData }
    }
}

impl Chan<Closed> {
    fn transcript(&self) -> &[u64] {
        &self.log
    }
}

fn main() {
    let c = Chan::new().send(1).send(2).close();
    #[cfg(send_after_close)]
    let c = c.send(3);
    #[cfg(close_twice)]
    let c = c.close();
    println!("transcript: {:?}", c.transcript());
}
