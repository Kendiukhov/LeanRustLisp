pub mod surface;
pub mod parser;
pub mod macro_expander;
pub mod elaborator;

pub use surface::*;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::macro_expander::Expander;

    #[test]
    fn test_parse_simple() {
        let input = "(lam x (sort 0) x)";
        let mut parser = Parser::new(input);
        let syntax = parser.parse().expect("Failed to parse");
        println!("Syntax: {:?}", syntax);
        assert_eq!(syntax.len(), 1);
    }

    #[test]
    fn test_expand_lam() {
         let input = "(lam x (sort 0) x)";
         let mut parser = Parser::new(input);
         let syntax = parser.parse().expect("Failed to parse");
         
         let mut expander = Expander::new();
         let term = expander.expand(syntax[0].clone()).expect("Failed to expand");
         println!("Expanded: {:?}", term);
         
         match term {
             SurfaceTerm::Lam(n, ty, body) => {
                 assert_eq!(n, "x");
             }
             _ => panic!("Expected Lam"),
         }
    }
}
