// Q10 (Rust): an owned value consumed in both branches of an `if` and of a `match` is
// accepted (only one branch runs). Using it after the branch is rejected.
//
// Variants (rustc --cfg <name>):
//   (none)      accepted
//   use_after   use the token after the `if` that consumed it: rejected (E0382)
//   one_branch  consume a token in one branch only and let the other branch ignore it:
//               ACCEPTED, because Rust is affine (an unused value is simply dropped);
//               a linear type system rejects this (see the Turnstile and Idris 2 programs)

struct Token(String); // owns a heap string; not Copy

fn close(t: Token) -> usize {
    t.0.len()
}

fn finish(t: Token) -> usize {
    t.0.len() * 2
}

enum Mode {
    Close,
    Finish,
}

fn main() {
    let flag = std::env::args().count() > 5; // false unless many arguments are given
    let t = Token(String::from("abc"));
    let r = if flag { close(t) } else { finish(t) };
    println!("if: {}", r);

    let mode = if flag { Mode::Close } else { Mode::Finish };
    let u = Token(String::from("abcd"));
    let s = match mode {
        Mode::Close => close(u),
        Mode::Finish => finish(u),
    };
    println!("match: {}", s);

    #[cfg(use_after)]
    println!("{}", t.0);

    #[cfg(one_branch)]
    {
        let w = Token(String::from("abcde"));
        let n = if flag { close(w) } else { 0 };
        println!("one_branch: {} (the token is dropped when flag is false)", n);
    }
}
