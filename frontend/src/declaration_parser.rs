use crate::surface::{Declaration, Syntax, SyntaxKind};
use crate::macro_expander::{Expander, ExpansionError};
use crate::parser::ParseError;
use kernel::ast::{AxiomTag, Totality, Transparency};
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

fn parse_axiom_tag(tag: &str) -> Result<AxiomTag, ExpansionError> {
    match tag {
        "classical" => Ok(AxiomTag::Classical),
        _ => Err(ExpansionError::InvalidSyntax(
            "axiom".to_string(),
            format!("Unknown axiom tag '{}'", tag),
        )),
    }
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
        let result = self.parse_decl_inner(syntax.clone());
        if let Err(ref e) = result {
             println!("Failed to parse decl: {:?}\nSyntax: {:?}", e, syntax.kind);
        }
        result
    }

    fn parse_decl_inner(&mut self, syntax: Syntax) -> Result<Option<Declaration>, DeclarationParseError> {
        // Clone syntax kind to inspect structure without moving parts of syntax
        match &syntax.kind {
            SyntaxKind::List(items) => {
                if items.is_empty() {
                    return Ok(None);
                }
                if let SyntaxKind::Symbol(s) = &items[0].kind {
                    match s.as_str() {
                        "def" => self.parse_def_with_transparency(items, "def", Totality::Total),
                        "partial" => self.parse_def_with_transparency(items, "partial", Totality::Partial),
                        "unsafe" => self.parse_def_with_transparency(items, "unsafe", Totality::Unsafe),
                        "opaque" => self.parse_def_fixed_transparency(items, "opaque", Totality::Total, Transparency::None),
                        "transparent" => self.parse_def_fixed_transparency(items, "transparent", Totality::Total, Transparency::Reducible),
                        "axiom" => {
                            if !(items.len() == 3 || items.len() == 4) {
                                return Err(ExpansionError::ArgumentCountMismatch("axiom".to_string(), 2, items.len() - 1).into());
                            }

                            let (tags_syntax, name_syntax, ty_syntax) = if items.len() == 3 {
                                (None, &items[1], &items[2])
                            } else {
                                (Some(&items[1]), &items[2], &items[3])
                            };

                            let mut tags = Vec::new();
                            if let Some(tag_node) = tags_syntax {
                                match &tag_node.kind {
                                    SyntaxKind::Symbol(tag) => {
                                        tags.push(parse_axiom_tag(tag)?);
                                    }
                                    SyntaxKind::List(tag_items) => {
                                        for tag_item in tag_items {
                                            if let SyntaxKind::Symbol(tag) = &tag_item.kind {
                                                tags.push(parse_axiom_tag(tag)?);
                                            } else {
                                                return Err(ExpansionError::InvalidSyntax(
                                                    "axiom".to_string(),
                                                    "Axiom tags must be symbols".to_string(),
                                                ).into());
                                            }
                                        }
                                    }
                                    _ => {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "axiom".to_string(),
                                            "Axiom tags must be a symbol or list of symbols".to_string(),
                                        ).into());
                                    }
                                }
                            }

                            let name = if let SyntaxKind::Symbol(n) = &name_syntax.kind {
                                n.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax("axiom".to_string(), "Name must be a symbol".to_string()).into());
                            };
                            let ty = self
                                .expander
                                .expand(ty_syntax.clone())?
                                .ok_or(ExpansionError::TransformationError("Type expanded to empty".to_string()))?;
                            Ok(Some(Declaration::Axiom { name, ty, tags }))
                        }
                        "inductive" => {
                            if items.len() < 3 {
                                return Err(ExpansionError::ArgumentCountMismatch("inductive".to_string(), 2, items.len() - 1).into());
                            }
                            let (is_copy, name_syntax, ty_syntax, ctor_slice) = match &items[1].kind {
                                SyntaxKind::Symbol(s) if s == "copy" => {
                                    if items.len() < 4 {
                                        return Err(ExpansionError::ArgumentCountMismatch("inductive".to_string(), 3, items.len() - 1).into());
                                    }
                                    (true, &items[2], &items[3], items.iter().skip(4))
                                }
                                _ => (false, &items[1], &items[2], items.iter().skip(3)),
                            };

                            let name = if let SyntaxKind::Symbol(n) = &name_syntax.kind {
                                n.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax("inductive".to_string(), "Name must be a symbol".to_string()).into());
                            };
                            let ty = self
                                .expander
                                .expand(ty_syntax.clone())?
                                .ok_or(ExpansionError::TransformationError("Type expanded to empty".to_string()))?;

                            let mut ctors = Vec::new();
                            for ctor_spec in ctor_slice {
                                if let SyntaxKind::List(citems) = &ctor_spec.kind {
                                    if citems.len() == 2 {
                                        // (Name Type)
                                        if let SyntaxKind::Symbol(cname) = &citems[0].kind {
                                            let cty = self.expander.expand(citems[1].clone())?.ok_or(ExpansionError::TransformationError("Constructor type expanded to empty".to_string()))?;
                                            ctors.push((cname.clone(), cty));
                                        } else { return Err(ExpansionError::InvalidSyntax("inductive ctor".to_string(), "Expected (Name Type)".to_string()).into()); }
                                    } else if citems.len() == 3 {
                                        // (Name : Type)
                                        if let SyntaxKind::Symbol(s) = &citems[1].kind {
                                            if s == ":" {
                                                if let SyntaxKind::Symbol(cname) = &citems[0].kind {
                                                    let cty = self.expander.expand(citems[2].clone())?.ok_or(ExpansionError::TransformationError("Constructor type expanded to empty".to_string()))?;
                                                    ctors.push((cname.clone(), cty));
                                                } else { return Err(ExpansionError::InvalidSyntax("inductive ctor".to_string(), "Expected (Name : Type)".to_string()).into()); }
                                            } else {
                                                 if let SyntaxKind::Symbol(cname) = &citems[1].kind {
                                                    let cty = self.expander.expand(citems[2].clone())?.ok_or(ExpansionError::TransformationError("Constructor type expanded to empty".to_string()))?;
                                                    ctors.push((cname.clone(), cty));
                                                } else { return Err(ExpansionError::InvalidSyntax("inductive ctor".to_string(), "Expected (Name : Type)".to_string()).into()); }
                                            }
                                        } else { return Err(ExpansionError::InvalidSyntax("inductive ctor".to_string(), "Expected (Name : Type)".to_string()).into()); }
                                    } else { return Err(ExpansionError::InvalidSyntax("inductive ctor".to_string(), "Expected (Name Type) or (Name : Type)".to_string()).into()); }
                                } else { return Err(ExpansionError::InvalidSyntax("inductive ctor".to_string(), "Expected list".to_string()).into()) }
                            }
                            Ok(Some(Declaration::Inductive { name, ty, ctors, is_copy }))
                        }
                        "defmacro" => {
                             if items.len() != 4 { return Err(ExpansionError::ArgumentCountMismatch("defmacro".to_string(), 3, items.len() - 1).into()); }
                             let name = if let SyntaxKind::Symbol(n) = &items[1].kind { n.clone() } else { return Err(ExpansionError::InvalidSyntax("defmacro".to_string(), "Name must be a symbol".to_string()).into()) };
                             
                             let mut args = Vec::new();
                             if let SyntaxKind::List(arg_list) = &items[2].kind {
                                 for arg in arg_list {
                                     if let SyntaxKind::Symbol(a) = &arg.kind {
                                         args.push(a.clone());
                                     } else { return Err(ExpansionError::InvalidSyntax("defmacro".to_string(), "Args must be symbols".to_string()).into()); }
                                 }
                             } else { return Err(ExpansionError::InvalidSyntax("defmacro".to_string(), "Arg list expected".to_string()).into()); }
                             
                             let body = items[3].clone();
                             self.expander.add_macro(name.clone(), args.clone(), body.clone());
                             Ok(Some(Declaration::DefMacro { name, args, body }))
                        }
                        _ => {
                             let expansion = self.expander.expand(syntax.clone())?;
                             if let Some(term) = expansion {
                                 Ok(Some(Declaration::Expr(term)))
                             } else {
                                 Ok(None)
                             }
                        }
                    }
                } else {
                     let expansion = self.expander.expand(syntax.clone())?;
                     if let Some(term) = expansion {
                         Ok(Some(Declaration::Expr(term)))
                     } else {
                         Ok(None)
                     }
                }
            },
             _ => {
                 let expansion = self.expander.expand(syntax.clone())?;
                 if let Some(term) = expansion {
                     Ok(Some(Declaration::Expr(term)))
                 } else {
                     Ok(None)
                 }
            }
        }
    }

    fn parse_def_with_transparency(
        &mut self,
        items: &[Syntax],
        head: &str,
        totality: Totality,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        let (name_index, transparency) = match items.len() {
            4 => (1, Transparency::Reducible),
            5 => {
                let attr = match &items[1].kind {
                    SyntaxKind::Symbol(attr) => attr.as_str(),
                    _ => {
                        return Err(ExpansionError::InvalidSyntax(
                            head.to_string(),
                            "Expected transparency attribute (opaque/transparent)".to_string(),
                        )
                        .into())
                    }
                };
                match attr {
                    "opaque" => (2, Transparency::None),
                    "transparent" => (2, Transparency::Reducible),
                    _ => {
                        return Err(ExpansionError::InvalidSyntax(
                            head.to_string(),
                            "Expected transparency attribute (opaque/transparent)".to_string(),
                        )
                        .into())
                    }
                }
            }
            _ => {
                return Err(
                    ExpansionError::ArgumentCountMismatch(head.to_string(), 3, items.len() - 1)
                        .into(),
                )
            }
        };

        self.parse_def_at(items, head, name_index, totality, transparency)
    }

    fn parse_def_fixed_transparency(
        &mut self,
        items: &[Syntax],
        head: &str,
        totality: Totality,
        transparency: Transparency,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        if items.len() != 4 {
            return Err(
                ExpansionError::ArgumentCountMismatch(head.to_string(), 3, items.len() - 1)
                    .into(),
            );
        }
        self.parse_def_at(items, head, 1, totality, transparency)
    }

    fn parse_def_at(
        &mut self,
        items: &[Syntax],
        head: &str,
        name_index: usize,
        totality: Totality,
        transparency: Transparency,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        let name = if let SyntaxKind::Symbol(n) = &items[name_index].kind {
            n.clone()
        } else {
            return Err(
                ExpansionError::InvalidSyntax(head.to_string(), "Name must be a symbol".to_string())
                    .into(),
            );
        };

        let ty = self
            .expander
            .expand(items[name_index + 1].clone())?
            .ok_or(ExpansionError::TransformationError(
                "Type expanded to empty".to_string(),
            ))?;
        let val = self
            .expander
            .expand(items[name_index + 2].clone())?
            .ok_or(ExpansionError::TransformationError(
                "Value expanded to empty".to_string(),
            ))?;

        Ok(Some(Declaration::Def {
            name,
            ty,
            val,
            totality,
            transparency,
        }))
    }
    
    // Add context to error if possible?
    // No, I'll just print it for now.
    /*
    fn handle_err<T>(&self, res: Result<T, ExpansionError>, syntax: &Syntax) -> Result<T, DeclarationParseError> {
        res.map_err(|e| {
            println!("Error parsing decl: {:?} \n Syntax: {:?}", e, syntax);
            e.into()
        })
    }
    */
}
