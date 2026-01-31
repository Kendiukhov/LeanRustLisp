use crate::ast::{Level, Term, BinderInfo};
use std::iter::Peekable;
use std::rc::Rc;
use std::str::Chars;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Unexpected EOF")]
    UnexpectedEof,
    #[error("Unexpected character: {0}")]
    UnexpectedChar(char),
    #[error("Expected {0}")]
    Expected(String),
    #[error("Unknown token: {0}")]
    UnknownToken(String),
}

#[derive(Debug, PartialEq, Eq)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
    Int(usize),
}

struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            chars: input.chars().peekable(),
        }
    }

    fn next_token(&mut self) -> Option<Result<Token, ParseError>> {
        self.skip_whitespace();
        let c = self.chars.next()?;
        match c {
            '(' => Some(Ok(Token::LParen)),
            ')' => Some(Ok(Token::RParen)),
            c if c.is_digit(10) => {
                let mut s = String::new();
                s.push(c);
                while let Some(&c) = self.chars.peek() {
                    if c.is_digit(10) {
                        s.push(self.chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                Some(Ok(Token::Int(s.parse().unwrap())))
            }
            c if !c.is_whitespace() => {
                let mut s = String::new();
                s.push(c);
                while let Some(&c) = self.chars.peek() {
                    if !c.is_whitespace() && c != '(' && c != ')' {
                        s.push(self.chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                Some(Ok(Token::Symbol(s)))
            }
            _ => None, // Should be unreachable due to skip_whitespace handling
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.chars.peek() {
            if c.is_whitespace() {
                self.chars.next();
            } else {
                break;
            }
        }
    }
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        Parser {
            lexer: Lexer::new(input),
        }
    }

    pub fn parse_term(&mut self) -> Result<Rc<Term>, ParseError> {
        match self.lexer.next_token() {
            Some(Ok(Token::Int(n))) => Ok(Term::var(n)),
            Some(Ok(Token::Symbol(s))) => {
                 if s == "Prop" {
                     Ok(Term::sort(Level::Zero))
                 } else if s == "Type" {
                     Ok(Term::sort(Level::Succ(Box::new(Level::Zero)))) // Type 0
                 } else {
                     Ok(Rc::new(Term::Const(s, vec![])))
                 }
            }
            Some(Ok(Token::LParen)) => {
                let head = self.expect_symbol()?;
                match head.as_str() {
                   "lam" => {
                       let ty = self.parse_term()?;
                       let body = self.parse_term()?;
                       self.expect_rparen()?;
                       Ok(Term::lam(ty, body, BinderInfo::Default))
                   }
                   "pi" => {
                       let ty = self.parse_term()?;
                       let body = self.parse_term()?;
                       self.expect_rparen()?;
                       Ok(Term::pi(ty, body, BinderInfo::Default))
                   }
                   "app" => {
                       let f = self.parse_term()?;
                       let a = self.parse_term()?;
                       self.expect_rparen()?;
                       Ok(Term::app(f, a))
                   }
                   "sort" => {
                       // simplified: (sort 0) -> Prop, (sort 1) -> Type 0
                       if let Some(Ok(Token::Int(0))) = self.lexer.next_token() {
                           self.expect_rparen()?;
                           Ok(Term::sort(Level::Zero))
                       } else {
                            // Hack for now
                           self.expect_rparen()?;
                           Ok(Term::sort(Level::Succ(Box::new(Level::Zero))))
                       }
                   }
                   "ind" => {
                       // (ind Name) - reference to inductive type
                       let name = self.expect_symbol()?;
                       self.expect_rparen()?;
                       Ok(Term::ind(name))
                   }
                   "ctor" => {
                       // (ctor IndName idx) - constructor reference
                       let ind_name = self.expect_symbol()?;
                       let idx = self.expect_int()?;
                       self.expect_rparen()?;
                       Ok(Term::ctor(ind_name, idx))
                   }
                   "rec" => {
                       // (rec IndName) - recursor reference
                       let name = self.expect_symbol()?;
                       self.expect_rparen()?;
                       Ok(Term::rec(name))
                   }
                   _ => Err(ParseError::UnknownToken(head)),
                }
            }
            Some(Err(e)) => Err(e),
            None => Err(ParseError::UnexpectedEof),
            _ => Err(ParseError::Expected("term".to_string())),
        }
    }

    fn expect_symbol(&mut self) -> Result<String, ParseError> {
        match self.lexer.next_token() {
            Some(Ok(Token::Symbol(s))) => Ok(s),
             _ => Err(ParseError::Expected("symbol".to_string())),
        }
    }

    fn expect_rparen(&mut self) -> Result<(), ParseError> {
        match self.lexer.next_token() {
            Some(Ok(Token::RParen)) => Ok(()),
            _ => Err(ParseError::Expected(")".to_string())),
        }
    }

    fn expect_int(&mut self) -> Result<usize, ParseError> {
        match self.lexer.next_token() {
            Some(Ok(Token::Int(n))) => Ok(n),
            _ => Err(ParseError::Expected("integer".to_string())),
        }
    }
}
