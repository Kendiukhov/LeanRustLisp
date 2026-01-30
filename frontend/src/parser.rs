use crate::surface::{Span, Syntax, SyntaxKind};
use std::iter::Peekable;
use std::str::Chars;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Unexpected EOF")]
    UnexpectedEof(Span),
    #[error("Unexpected character: {0}")]
    UnexpectedChar(char, Span),
     #[error("Unmatched parenthesis")]
    UnmatchedParen(Span),
}

struct Lexer<'a> {
    input: &'a str,
    chars: Peekable<Chars<'a>>,
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            input,
            chars: input.chars().peekable(),
            pos: 0,
            line: 1,
            col: 0,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn next(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        self.pos += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    fn current_span(&self) -> Span {
        Span {
            start: self.pos,
            end: self.pos,
            line: self.line,
            col: self.col,
        }
    }
    
    // Simplistic skipping with comments
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.next();
            } else if c == ';' {
                // Comment: skip until newline
                while let Some(nc) = self.peek() {
                    if nc == '\n' {
                         break; 
                    }
                    self.next();
                }
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

    pub fn parse(&mut self) -> Result<Vec<Syntax>, ParseError> {
        let mut exprs = Vec::new();
        self.lexer.skip_whitespace();
        while self.lexer.peek().is_some() {
            exprs.push(self.parse_expr()?);
            self.lexer.skip_whitespace();
        }
        Ok(exprs)
    }

    fn parse_expr(&mut self) -> Result<Syntax, ParseError> {
        self.lexer.skip_whitespace();
        let start_span = self.lexer.current_span();
        
        match self.lexer.peek() {
            Some('(') => {
                self.lexer.next(); // eat '('
                let mut list = Vec::new();
                loop {
                    self.lexer.skip_whitespace();
                    match self.lexer.peek() {
                        Some(')') => {
                             self.lexer.next(); // eat ')'
                             let end_span = self.lexer.current_span();
                             return Ok(Syntax {
                                 kind: SyntaxKind::List(list),
                                 span: Span { start: start_span.start, end: end_span.end, line: start_span.line, col: start_span.col },
                                 scopes: Vec::new(),
                             });
                        }
                        None => return Err(ParseError::UnexpectedEof(self.lexer.current_span())),
                        _ => {
                            list.push(self.parse_expr()?);
                        }
                    }
                }
            }
            Some(c) if c.is_digit(10) => {
                let mut s = String::new();
                while let Some(c) = self.lexer.peek() {
                    if c.is_digit(10) {
                        s.push(self.lexer.next().unwrap());
                    } else {
                        break;
                    }
                }
                let end_span = self.lexer.current_span();
                Ok(Syntax {
                    kind: SyntaxKind::Int(s.parse().unwrap()),
                    span: Span { start: start_span.start, end: end_span.end, line: start_span.line, col: start_span.col },
                    scopes: Vec::new(),
                })
            }
            Some(_) => {
                let mut s = String::new();
                while let Some(c) = self.lexer.peek() {
                    if !c.is_whitespace() && c != '(' && c != ')' {
                        s.push(self.lexer.next().unwrap());
                    } else {
                        break;
                    }
                }
                let end_span = self.lexer.current_span();
                if s.is_empty() {
                     return Err(ParseError::UnexpectedChar(self.lexer.peek().unwrap_or('\0'), start_span));
                }
                Ok(Syntax {
                    kind: SyntaxKind::Symbol(s),
                    span: Span { start: start_span.start, end: end_span.end, line: start_span.line, col: start_span.col },
                    scopes: Vec::new(),
                })
            }
            None => Err(ParseError::UnexpectedEof(start_span)),
        }
    }
}
