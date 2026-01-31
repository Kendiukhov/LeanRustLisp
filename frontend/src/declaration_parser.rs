use crate::surface::{Declaration, SurfaceTerm, Syntax, SyntaxKind};
use crate::macro_expander::{Expander, ExpansionError};
use crate::parser::ParseError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DeclarationParseError {
    #[error("Expansion error: {0}")]
    Expansion(#[from] ExpansionError),
    #[error("Parse error: {0}")]
    Parse(#[from] ParseError),
}

pub struct DeclarationParser<'a> {
    expander: &'a mut Expander,
}

impl<'a> DeclarationParser<'a> {
    pub fn new(expander: &'a mut Expander) -> Self {
        DeclarationParser { expander }
    }

    pub fn parse(&mut self, syntax_nodes: Vec<Syntax>) -> Result<Vec<Declaration>, DeclarationParseError> {
        let mut decls = Vec::new();
        for syntax in syntax_nodes {
            if let Some(decl) = self.parse_decl(syntax)? {
                decls.push(decl);
            }
        }
        Ok(decls)
    }

    fn parse_decl(&mut self, syntax: Syntax) -> Result<Option<Declaration>, DeclarationParseError> {
        if let SyntaxKind::List(items) = syntax.kind {
            if items.is_empty() {
                return Ok(None);
            }
            if let SyntaxKind::Symbol(s) = &items[0].kind {
                match s.as_str() {
                    "def" | "partial" => {
                        let is_partial = s == "partial";
                        if items.len() != 4 { return Err(ExpansionError::TransformationError.into()); }
                        let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { return Err(ExpansionError::TransformationError.into()) };
                        
                        let ty = self.expander.expand(items[2].clone())?.ok_or(ExpansionError::TransformationError)?;
                        let val = self.expander.expand(items[3].clone())?.ok_or(ExpansionError::TransformationError)?;

                        Ok(Some(Declaration::Def { name, ty, val, is_partial }))
                    }
                    "axiom" => {
                        if items.len() != 3 { return Err(ExpansionError::TransformationError.into()); }
                        let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { return Err(ExpansionError::TransformationError.into()) };
                        let ty = self.expander.expand(items[2].clone())?.ok_or(ExpansionError::TransformationError)?;
                        Ok(Some(Declaration::Axiom { name, ty }))
                    }
                    "inductive" => {
                        if items.len() < 3 { return Err(ExpansionError::TransformationError.into()); }
                        let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { return Err(ExpansionError::TransformationError.into()) };
                        let ty = self.expander.expand(items[2].clone())?.ok_or(ExpansionError::TransformationError)?;
                        
                        let mut ctors = Vec::new();
                        for ctor_spec in items.iter().skip(3) {
                            if let SyntaxKind::List(citems) = &ctor_spec.kind {
                                if citems.len() == 2 {
                                    // (Name Type)
                                    if let SyntaxKind::Symbol(cname) = &citems[0].kind {
                                        let cty = self.expander.expand(citems[1].clone())?.ok_or(ExpansionError::TransformationError)?;
                                        ctors.push((cname.clone(), cty));
                                    } else { return Err(ExpansionError::TransformationError.into()); }
                                } else if citems.len() == 3 {
                                    // (Name : Type)
                                    if let SyntaxKind::Symbol(s) = &citems[1].kind {
                                        if s == ":" {
                                            if let SyntaxKind::Symbol(cname) = &citems[0].kind {
                                                let cty = self.expander.expand(citems[2].clone())?.ok_or(ExpansionError::TransformationError)?;
                                                ctors.push((cname.clone(), cty));
                                            } else { return Err(ExpansionError::TransformationError.into()); }
                                        } else {
                                            // Maybe (ignore Name Type)? Legacy support?
                                            // Let's assume (Name : Type) checks strictly for colon
                                             if let SyntaxKind::Symbol(cname) = &citems[1].kind {
                                                let cty = self.expander.expand(citems[2].clone())?.ok_or(ExpansionError::TransformationError)?;
                                                ctors.push((cname.clone(), cty));
                                            } else { return Err(ExpansionError::TransformationError.into()); }
                                        }
                                    } else { return Err(ExpansionError::TransformationError.into()); }
                                } else { return Err(ExpansionError::TransformationError.into()); }
                            } else { return Err(ExpansionError::TransformationError.into()) }
                        }
                        Ok(Some(Declaration::Inductive { name, ty, ctors }))
                    }
                    "defmacro" => {
                        if items.len() != 4 { return Err(ExpansionError::TransformationError.into()); }
                        let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { return Err(ExpansionError::TransformationError.into()) };
                        
                        let mut args = Vec::new();
                        if let SyntaxKind::List(arg_list) = &items[2].kind {
                            for arg in arg_list {
                                if let SyntaxKind::Symbol(a) = &arg.kind {
                                    args.push(a.clone());
                                } else { return Err(ExpansionError::TransformationError.into()); }
                            }
                        } else { return Err(ExpansionError::TransformationError.into()); }
                        
                        let body = items[3].clone();
                        Ok(Some(Declaration::DefMacro { name, args, body }))
                    }
                    _ => {
                        let term = self.expander.expand(Syntax { kind: SyntaxKind::List(items), ..syntax })?.ok_or(ExpansionError::TransformationError)?;
                        Ok(Some(Declaration::Expr(term)))
                    }
                }
            } else {
                let term = self.expander.expand(Syntax { kind: SyntaxKind::List(items), ..syntax })?.ok_or(ExpansionError::TransformationError)?;
                Ok(Some(Declaration::Expr(term)))
            }
        } else {
            let term = self.expander.expand(syntax)?.ok_or(ExpansionError::TransformationError)?;
            Ok(Some(Declaration::Expr(term)))
        }
    }
}
