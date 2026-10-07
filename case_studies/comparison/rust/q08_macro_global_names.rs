// Q8 (Rust, macro_rules!): how a template's reference to a *global* (item) name is resolved.
//
// macro_rules! has "mixed-site" hygiene: local variables and labels are resolved at the
// definition site, but item names (functions, types, ...) are resolved at the invocation site.
// `call_helper!` mentions `helper` unqualified; invoked from module `user`, which defines its
// own `helper`, it calls `user::helper`. The documented way to pin the definition-site item
// is a `$crate::` path, as in `call_helper_pinned!`.

mod lib {
    pub fn helper() -> &'static str {
        "lib::helper (definition site)"
    }

    macro_rules! call_helper {
        () => {
            helper()
        };
    }

    macro_rules! call_helper_pinned {
        () => {
            $crate::lib::helper()
        };
    }

    pub(crate) use call_helper;
    pub(crate) use call_helper_pinned;
}

mod user {
    pub fn helper() -> &'static str {
        "user::helper (use site)"
    }

    pub fn run() {
        println!("call_helper!()        -> {}", crate::lib::call_helper!());
        println!("call_helper_pinned!() -> {}", crate::lib::call_helper_pinned!());
    }
}

fn main() {
    let _ = lib::helper;
    user::run();
}
