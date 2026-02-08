use crate::surface::{Span, Syntax, SyntaxKind};
use std::iter::Peekable;
use std::num::IntErrorKind;
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
    #[error("Invalid integer literal: {0}")]
    InvalidIntegerLiteral(String, Span),
    #[error("Integer literal out of range for i64: {0}")]
    IntegerOverflow(String, Span),
    #[error("Invalid float literal: {0}")]
    InvalidFloatLiteral(String, Span),
}

impl ParseError {
    pub fn span(&self) -> Span {
        match self {
            ParseError::UnexpectedEof(span)
            | ParseError::UnexpectedChar(_, span)
            | ParseError::UnmatchedParen(span)
            | ParseError::InvalidIntegerLiteral(_, span)
            | ParseError::IntegerOverflow(_, span)
            | ParseError::InvalidFloatLiteral(_, span) => *span,
        }
    }

    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            ParseError::UnexpectedEof(_) => "F0001",
            ParseError::UnexpectedChar(_, _) => "F0002",
            ParseError::UnmatchedParen(_) => "F0003",
            ParseError::InvalidIntegerLiteral(_, _) => "F0004",
            ParseError::IntegerOverflow(_, _) => "F0005",
            ParseError::InvalidFloatLiteral(_, _) => "F0006",
        }
    }
}

struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            chars: input.chars().peekable(),
            pos: 0,
            line: 1,
            col: 0,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn peek_second(&self) -> Option<char> {
        let mut cloned = self.chars.clone();
        cloned.next()?;
        cloned.next()
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
        let mut expr = self.parse_primary()?;

        loop {
            self.lexer.skip_whitespace();
            if self.lexer.peek() != Some('[') {
                break;
            }

            let start_span = expr.span;
            self.lexer.next(); // eat '['
            self.lexer.skip_whitespace();
            let index_expr = self.parse_expr()?;
            self.lexer.skip_whitespace();
            match self.lexer.peek() {
                Some(']') => {
                    self.lexer.next(); // eat ']'
                }
                Some(c) => {
                    return Err(ParseError::UnexpectedChar(c, self.lexer.current_span()));
                }
                None => return Err(ParseError::UnexpectedEof(self.lexer.current_span())),
            }
            let end_span = self.lexer.current_span();
            expr = Syntax {
                kind: SyntaxKind::Index(Box::new(expr), Box::new(index_expr)),
                span: Span {
                    start: start_span.start,
                    end: end_span.end,
                    line: start_span.line,
                    col: start_span.col,
                },
                scopes: Vec::new(),
            };
        }

        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Syntax, ParseError> {
        self.lexer.skip_whitespace();
        let start_span = self.lexer.current_span();

        match self.lexer.peek() {
            Some(')') => Err(ParseError::UnmatchedParen(start_span)),
            Some('"') => {
                self.lexer.next(); // eat opening quote
                let mut s = String::new();
                loop {
                    match self.lexer.next() {
                        Some('"') => break,
                        Some('\\') => match self.lexer.next() {
                            Some('n') => s.push('\n'),
                            Some('r') => s.push('\r'),
                            Some('t') => s.push('\t'),
                            Some('"') => s.push('"'),
                            Some('\\') => s.push('\\'),
                            Some(other) => {
                                s.push('\\');
                                s.push(other);
                            }
                            None => return Err(ParseError::UnexpectedEof(start_span)),
                        },
                        Some(c) => s.push(c),
                        None => return Err(ParseError::UnexpectedEof(start_span)),
                    }
                }
                let end_span = self.lexer.current_span();
                Ok(Syntax {
                    kind: SyntaxKind::String(s),
                    span: Span {
                        start: start_span.start,
                        end: end_span.end,
                        line: start_span.line,
                        col: start_span.col,
                    },
                    scopes: Vec::new(),
                })
            }
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
                                span: Span {
                                    start: start_span.start,
                                    end: end_span.end,
                                    line: start_span.line,
                                    col: start_span.col,
                                },
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
            Some('{') => {
                self.lexer.next(); // eat '{'
                let mut list = Vec::new();
                loop {
                    self.lexer.skip_whitespace();
                    match self.lexer.peek() {
                        Some('}') => {
                            self.lexer.next(); // eat '}'
                            let end_span = self.lexer.current_span();
                            return Ok(Syntax {
                                kind: SyntaxKind::BracedList(list),
                                span: Span {
                                    start: start_span.start,
                                    end: end_span.end,
                                    line: start_span.line,
                                    col: start_span.col,
                                },
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
            Some('\'') => {
                self.lexer.next(); // eat '
                let inner = self.parse_expr()?;
                let end_span = inner.span;
                Ok(Syntax {
                    kind: SyntaxKind::List(vec![
                        Syntax {
                            kind: SyntaxKind::Symbol("quote".to_string()),
                            span: start_span,
                            scopes: vec![],
                        },
                        inner,
                    ]),
                    span: Span {
                        start: start_span.start,
                        end: end_span.end,
                        line: start_span.line,
                        col: start_span.col,
                    },
                    scopes: Vec::new(),
                })
            }
            Some('`') => {
                self.lexer.next(); // eat `
                let inner = self.parse_expr()?;
                let end_span = inner.span;
                Ok(Syntax {
                    kind: SyntaxKind::List(vec![
                        Syntax {
                            kind: SyntaxKind::Symbol("quasiquote".to_string()),
                            span: start_span,
                            scopes: vec![],
                        },
                        inner,
                    ]),
                    span: Span {
                        start: start_span.start,
                        end: end_span.end,
                        line: start_span.line,
                        col: start_span.col,
                    },
                    scopes: Vec::new(),
                })
            }
            Some(',') => {
                self.lexer.next();
                if self.lexer.peek() == Some('@') {
                    self.lexer.next(); // eat @
                    let inner = self.parse_expr()?;
                    let end_span = inner.span;
                    Ok(Syntax {
                        kind: SyntaxKind::List(vec![
                            Syntax {
                                kind: SyntaxKind::Symbol("unquote-splicing".to_string()),
                                span: start_span,
                                scopes: vec![],
                            },
                            inner,
                        ]),
                        span: Span {
                            start: start_span.start,
                            end: end_span.end,
                            line: start_span.line,
                            col: start_span.col,
                        },
                        scopes: Vec::new(),
                    })
                } else {
                    let inner = self.parse_expr()?;
                    let end_span = inner.span;
                    Ok(Syntax {
                        kind: SyntaxKind::List(vec![
                            Syntax {
                                kind: SyntaxKind::Symbol("unquote".to_string()),
                                span: start_span,
                                scopes: vec![],
                            },
                            inner,
                        ]),
                        span: Span {
                            start: start_span.start,
                            end: end_span.end,
                            line: start_span.line,
                            col: start_span.col,
                        },
                        scopes: Vec::new(),
                    })
                }
            }
            Some(c) if c.is_ascii_digit() => {
                let mut s = String::new();
                while let Some(c) = self.lexer.peek() {
                    if c.is_ascii_digit() {
                        let next_digit = self
                            .lexer
                            .next()
                            .ok_or_else(|| ParseError::UnexpectedEof(self.lexer.current_span()))?;
                        s.push(next_digit);
                    } else {
                        break;
                    }
                }
                if self.lexer.peek() == Some('.')
                    && self
                        .lexer
                        .peek_second()
                        .is_some_and(|next| next.is_ascii_digit())
                {
                    s.push(
                        self.lexer
                            .next()
                            .ok_or_else(|| ParseError::UnexpectedEof(self.lexer.current_span()))?,
                    );
                    while let Some(c) = self.lexer.peek() {
                        if c.is_ascii_digit() {
                            s.push(self.lexer.next().ok_or_else(|| {
                                ParseError::UnexpectedEof(self.lexer.current_span())
                            })?);
                        } else {
                            break;
                        }
                    }
                }
                let end_span = self.lexer.current_span();
                let literal_span = Span {
                    start: start_span.start,
                    end: end_span.end,
                    line: start_span.line,
                    col: start_span.col,
                };
                if Self::looks_like_float_token(&s) {
                    s.parse::<f32>()
                        .map_err(|_| ParseError::InvalidFloatLiteral(s.clone(), literal_span))?;
                    return Ok(Syntax {
                        kind: SyntaxKind::Float(s),
                        span: literal_span,
                        scopes: Vec::new(),
                    });
                }
                let parsed = s.parse::<i64>().map_err(|err| match err.kind() {
                    IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => {
                        ParseError::IntegerOverflow(s.clone(), literal_span)
                    }
                    _ => ParseError::InvalidIntegerLiteral(s.clone(), literal_span),
                })?;
                Ok(Syntax {
                    kind: SyntaxKind::Int(parsed),
                    span: literal_span,
                    scopes: Vec::new(),
                })
            }
            Some(_) => {
                let mut s = String::new();
                while let Some(c) = self.lexer.peek() {
                    if !c.is_whitespace()
                        && c != '('
                        && c != ')'
                        && c != '{'
                        && c != '}'
                        && c != '['
                        && c != ']'
                    {
                        let next_char = self
                            .lexer
                            .next()
                            .ok_or_else(|| ParseError::UnexpectedEof(self.lexer.current_span()))?;
                        s.push(next_char);
                    } else {
                        break;
                    }
                }
                let end_span = self.lexer.current_span();
                if s.is_empty() {
                    return Err(ParseError::UnexpectedChar(
                        self.lexer.peek().unwrap_or('\0'),
                        start_span,
                    ));
                }
                if Self::looks_like_integer_token(&s) {
                    let literal_span = Span {
                        start: start_span.start,
                        end: end_span.end,
                        line: start_span.line,
                        col: start_span.col,
                    };
                    let parsed = s.parse::<i64>().map_err(|err| match err.kind() {
                        IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => {
                            ParseError::IntegerOverflow(s.clone(), literal_span)
                        }
                        _ => ParseError::InvalidIntegerLiteral(s.clone(), literal_span),
                    })?;
                    Ok(Syntax {
                        kind: SyntaxKind::Int(parsed),
                        span: literal_span,
                        scopes: Vec::new(),
                    })
                } else if Self::looks_like_float_token(&s) {
                    let literal_span = Span {
                        start: start_span.start,
                        end: end_span.end,
                        line: start_span.line,
                        col: start_span.col,
                    };
                    s.parse::<f32>()
                        .map_err(|_| ParseError::InvalidFloatLiteral(s.clone(), literal_span))?;
                    Ok(Syntax {
                        kind: SyntaxKind::Float(s),
                        span: literal_span,
                        scopes: Vec::new(),
                    })
                } else if s == "_" {
                    Ok(Syntax {
                        kind: SyntaxKind::Hole,
                        span: Span {
                            start: start_span.start,
                            end: end_span.end,
                            line: start_span.line,
                            col: start_span.col,
                        },
                        scopes: Vec::new(),
                    })
                } else {
                    Ok(Syntax {
                        kind: SyntaxKind::Symbol(s),
                        span: Span {
                            start: start_span.start,
                            end: end_span.end,
                            line: start_span.line,
                            col: start_span.col,
                        },
                        scopes: Vec::new(),
                    })
                }
            }
            None => Err(ParseError::UnexpectedEof(start_span)),
        }
    }

    fn looks_like_integer_token(token: &str) -> bool {
        if token.is_empty() {
            return false;
        }
        if let Some(rest) = token.strip_prefix('-') {
            !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
        } else {
            token.chars().all(|c| c.is_ascii_digit())
        }
    }

    fn looks_like_float_token(token: &str) -> bool {
        let body = if let Some(rest) = token.strip_prefix('-') {
            rest
        } else {
            token
        };
        let mut parts = body.split('.');
        let Some(integer_part) = parts.next() else {
            return false;
        };
        let Some(fractional_part) = parts.next() else {
            return false;
        };
        if parts.next().is_some() {
            return false;
        }
        !integer_part.is_empty()
            && !fractional_part.is_empty()
            && integer_part.chars().all(|c| c.is_ascii_digit())
            && fractional_part.chars().all(|c| c.is_ascii_digit())
    }
}
