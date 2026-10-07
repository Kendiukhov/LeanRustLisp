// Q5 (Rust): a single-use channel. `send` takes the channel by value, so after one send
// the channel has been moved and any further use is a compile-time error (E0382).
// `Chan` is neither `Copy` nor `Clone`, so there is no way to duplicate it.
//
// Variants (rustc --cfg <name>):
//   (none)  one send: accepted
//   reuse   a second send on the same channel: rejected (E0382, use of moved value)

struct Chan {
    id: u32,
}

impl Chan {
    fn send(self, x: u64) {
        println!("sent {} on channel {}", x, self.id);
    }
}

fn main() {
    let c = Chan { id: 1 };
    c.send(7);
    #[cfg(reuse)]
    c.send(8);
}
