// Q8 (Rust, macro_rules!): a hygienic macro that generates typed operations, and a template
// binder that does not capture a user variable.
//
// `def_unit!` generates a newtype and its operations; the generated code is type-checked like
// hand-written code, so mixing two generated units is a type error. `with_tmp!` binds `tmp`
// in its template and evaluates the user's expression in that scope; macro_rules! local
// variables are hygienic, so the user's `tmp` is not captured (result 101, not 2).
//
// Variants (rustc --cfg <name>):
//   (none)     accepted; prints the generated operations' results and with_tmp!(tmp) = 101
//   mix_units  add a `Seconds` to a `Meters`: rejected (E0308)

macro_rules! def_unit {
    ($unit:ident, $repr:ty) => {
        #[derive(Debug, Clone, Copy, PartialEq)]
        struct $unit($repr);
        impl $unit {
            fn add(self, other: $unit) -> $unit {
                let tmp = self.0 + other.0;
                $unit(tmp)
            }
            fn get(self) -> $repr {
                self.0
            }
        }
    };
}

def_unit!(Meters, u64);
def_unit!(Seconds, u64);

macro_rules! with_tmp {
    ($e:expr) => {{
        let tmp = 1u64;
        $e + tmp
    }};
}

fn main() {
    let d = Meters(3).add(Meters(4));
    let t = Seconds(5).add(Seconds(6));
    println!("Meters(3).add(Meters(4)) = {}, Seconds(5).add(Seconds(6)) = {}", d.get(), t.get());

    let tmp = 100u64;
    println!("with_tmp!(tmp) = {} (101 = hygienic, 2 = captured)", with_tmp!(tmp));

    #[cfg(mix_units)]
    let _bad = Meters(3).add(Seconds(4));
}
