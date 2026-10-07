// Q9 (Rust): two simultaneously live mutable references to the same variable are rejected.
//
// Variants (rustc --cfg <name>):
//   (none)      two &mut to *different* variables in one call, and two &mut to the same
//               variable whose lifetimes do not overlap (NLL): accepted
//   alias_call  `bump(&mut x, &mut x)`: rejected (E0499)
//   alias_live  `let r1 = &mut x; let r2 = &mut x; *r1 += 1;`: rejected (E0499)

fn bump(a: &mut u64, b: &mut u64) {
    *a += 1;
    *b += 10;
}

fn main() {
    let mut x = 0u64;
    let mut y = 0u64;
    bump(&mut x, &mut y);

    let r1 = &mut x;
    *r1 += 1; // last use of r1
    let r2 = &mut x;
    *r2 += 1;

    #[cfg(alias_call)]
    bump(&mut x, &mut x);

    #[cfg(alias_live)]
    {
        let r1 = &mut x;
        let r2 = &mut x;
        *r1 += 1;
        *r2 += 1;
    }

    println!("x = {}, y = {}", x, y);
}
