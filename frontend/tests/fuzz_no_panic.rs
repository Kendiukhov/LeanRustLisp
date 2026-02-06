use frontend::declaration_parser::DeclarationParser;
use frontend::elaborator::Elaborator;
use frontend::macro_expander::Expander;
use frontend::parser::Parser;
use frontend::surface::Declaration;
use kernel::checker::Env;
use std::panic::{catch_unwind, AssertUnwindSafe};

struct Lcg {
    state: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        // Constants from Numerical Recipes
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }

    fn gen_range(&mut self, max: usize) -> usize {
        if max == 0 {
            return 0;
        }
        (self.next() as usize) % max
    }
}

fn random_program(rng: &mut Lcg) -> String {
    const TOKENS: &[&str] = &[
        "(",
        ")",
        "def",
        "lam",
        "pi",
        "Type",
        "Prop",
        "Nat",
        "Bool",
        "match",
        "case",
        "zero",
        "succ",
        "true",
        "false",
        "let",
        "in",
        "axiom",
        "inductive",
        "macro",
        " ",
        "\n",
        "\t",
        "0",
        "1",
        "2",
        "3",
        "x",
        "y",
        "z",
        "A",
        "B",
    ];

    let token_count = 8 + rng.gen_range(48);
    let mut out = String::new();
    for _ in 0..token_count {
        let tok = TOKENS[rng.gen_range(TOKENS.len())];
        out.push_str(tok);
        if rng.gen_range(5) == 0 {
            out.push(' ');
        }
    }
    out
}

#[test]
fn fuzz_parser_and_expander_no_panic() {
    let mut rng = Lcg::new(0x5EED_F00D);

    for _ in 0..200 {
        let input = random_program(&mut rng);

        let parse_result = catch_unwind(AssertUnwindSafe(|| {
            let mut parser = Parser::new(&input);
            parser.parse()
        }));

        assert!(parse_result.is_ok(), "Parser panicked on input: {}", input);

        if let Ok(Ok(syntax_nodes)) = parse_result {
            let expand_result = catch_unwind(AssertUnwindSafe(|| {
                let mut expander = Expander::new();
                let mut decl_parser = DeclarationParser::new(&mut expander);
                let _ = decl_parser.parse(syntax_nodes);
            }));

            assert!(
                expand_result.is_ok(),
                "Macro expansion panicked on input: {}",
                input
            );
        }
    }
}

#[test]
fn fuzz_parser_expander_elaborator_no_panic() {
    let mut rng = Lcg::new(0xC0FF_EE);

    for _ in 0..200 {
        let input = random_program(&mut rng);

        let parse_result = catch_unwind(AssertUnwindSafe(|| {
            let mut parser = Parser::new(&input);
            parser.parse()
        }));

        assert!(parse_result.is_ok(), "Parser panicked on input: {}", input);

        if let Ok(Ok(syntax_nodes)) = parse_result {
            let expand_result = catch_unwind(AssertUnwindSafe(|| {
                let mut expander = Expander::new();
                let mut decl_parser = DeclarationParser::new(&mut expander);
                decl_parser.parse(syntax_nodes)
            }));

            assert!(
                expand_result.is_ok(),
                "Macro expansion panicked on input: {}",
                input
            );

            if let Ok(Ok(decls)) = expand_result {
                let env = Env::new();
                for decl in decls {
                    let elab_result = catch_unwind(AssertUnwindSafe(|| {
                        let mut elab = Elaborator::new(&env);
                        match decl {
                            Declaration::Def { ty, val, .. } => {
                                if let Ok((ty_core, _)) = elab.infer(ty) {
                                    let _ = elab.check(val, &ty_core);
                                    let _ = elab.solve_constraints();
                                }
                            }
                            Declaration::Axiom { ty, .. } => {
                                let _ = elab.infer(ty);
                                let _ = elab.solve_constraints();
                            }
                            Declaration::Inductive { ty, ctors, .. } => {
                                let _ = elab.infer(ty);
                                for (_, cty) in ctors {
                                    let _ = elab.infer(cty);
                                }
                                let _ = elab.solve_constraints();
                            }
                            Declaration::Instance {
                                head, requirements, ..
                            } => {
                                let _ = elab.infer(head);
                                for req in requirements {
                                    let _ = elab.infer(req);
                                }
                                let _ = elab.solve_constraints();
                            }
                            Declaration::Expr(term) => {
                                let _ = elab.infer(term);
                                let _ = elab.solve_constraints();
                            }
                            Declaration::DefMacro { .. } => {}
                            Declaration::Module { .. } => {}
                            Declaration::ImportClassical => {}
                            Declaration::ImportModule { .. } => {}
                            Declaration::OpenModule { .. } => {}
                        }
                    }));

                    assert!(
                        elab_result.is_ok(),
                        "Elaborator panicked on input: {}",
                        input
                    );
                }
            }
        }
    }
}
