// Q12 (Rust): a once-only closure called twice is rejected at compile time.
//
// The closure moves a captured `String` out of its environment, so it only implements
// `FnOnce`; calling it consumes it.
//
// Variants (rustc --cfg <name>):
//   (none)      called once: accepted
//   call_twice  called a second time: rejected (E0382, use of moved value)
//   as_fn       passed where an `Fn` (callable many times) is required: rejected (E0525)
//   in_loop     a loop body (which runs many times) moves a captured-from-outside String:
//               rejected (E0382, value moved in a previous iteration of the loop)

fn call_many<F: Fn() -> usize>(f: F) -> usize {
    f() + f()
}

fn main() {
    let token = String::from("secret");
    let consume = move || {
        let t = token; // moves the captured String out: FnOnce
        t.len()
    };
    println!("first call: {}", consume());

    #[cfg(call_twice)]
    println!("second call: {}", consume());

    let _ = call_many(|| 1);
    #[cfg(as_fn)]
    {
        let token2 = String::from("again");
        let consume2 = move || {
            let t = token2;
            t.len()
        };
        println!("{}", call_many(consume2));
    }

    #[cfg(in_loop)]
    {
        let token3 = String::from("loop");
        let mut total = 0;
        for _ in 0..3 {
            let t = token3;
            total += t.len();
        }
        println!("{}", total);
    }
}
