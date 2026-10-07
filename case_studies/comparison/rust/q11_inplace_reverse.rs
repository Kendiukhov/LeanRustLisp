// Q11 (Rust): in-place update. `Vec::reverse` reverses in the existing buffer, also behind a
// value-passing ("functional") signature `fn(Vec<T>) -> Vec<T>`. The static side: while the
// vector is reversed nobody else can observe it, because a live shared borrow (E0502) and a
// use of the moved-from vector (E0382) are both compile-time errors.
//
// Variants (rustc --cfg <name>):
//   (none)          accepted; prints whether the buffer pointer is unchanged
//   shared_alias    reverse while a shared reference is still in use: rejected (E0502)
//   use_after_move  read the vector after passing it to rev_owned: rejected (E0382)

fn rev_owned(mut v: Vec<u64>) -> Vec<u64> {
    v.reverse();
    v
}

fn main() {
    let mut v: Vec<u64> = (0..8).collect();
    let p0 = v.as_ptr();
    let cap0 = v.capacity();
    v.reverse();
    println!(
        "Vec::reverse: same buffer = {}, same capacity = {}, v = {:?}",
        p0 == v.as_ptr(),
        cap0 == v.capacity(),
        v
    );

    #[cfg(shared_alias)]
    {
        let r = &v;
        v.reverse();
        println!("{:?}", r);
    }

    let p1 = v.as_ptr();
    let w = rev_owned(v);
    println!("rev_owned (by value): same buffer = {}, w = {:?}", p1 == w.as_ptr(), w);

    #[cfg(use_after_move)]
    println!("{:?}", v);

    // Contrast: an iterator-based reverse builds a new vector in a new buffer.
    let p2 = w.as_ptr();
    let z: Vec<u64> = w.iter().rev().copied().collect();
    println!("iter().rev().collect(): same buffer = {}, z = {:?}", p2 == z.as_ptr(), z);
}
