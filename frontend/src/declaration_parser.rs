use crate::desugar::Desugarer;
use crate::macro_expander::{is_reserved_macro_name, Expander, ExpansionError};
use crate::parser::ParseError;
use crate::surface::{Declaration, Span, Syntax, SyntaxKind};
use kernel::ast::{AxiomTag, Totality, Transparency};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DeclarationParseError {
    #[error("Expansion error: {0}")]
    Expansion(#[from] ExpansionError),
    #[error("Parse error: {0}")]
    Parse(#[from] ParseError),
}

impl DeclarationParseError {
    pub fn diagnostic_code(&self) -> &'static str {
        match self {
            DeclarationParseError::Expansion(err) => err.diagnostic_code(),
            DeclarationParseError::Parse(err) => err.diagnostic_code(),
        }
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            DeclarationParseError::Expansion(_) => None,
            DeclarationParseError::Parse(err) => Some(err.span()),
        }
    }
}

pub struct DeclarationParser<'a> {
    expander: &'a mut Expander,
    desugarer: Desugarer,
}

fn parse_axiom_tag(tag: &str) -> Result<AxiomTag, ExpansionError> {
    match tag {
        "classical" => Ok(AxiomTag::Classical),
        "unsafe" => Ok(AxiomTag::Unsafe),
        _ => Err(ExpansionError::InvalidSyntax(
            "axiom".to_string(),
            format!("Unknown axiom tag '{}'", tag),
        )),
    }
}

fn parse_inductive_attr_list(
    list: &[Syntax],
    is_copy: &mut bool,
    attrs: &mut Vec<String>,
) -> Result<(), ExpansionError> {
    for attr in list {
        match &attr.kind {
            SyntaxKind::Symbol(s) => {
                if s == "copy" {
                    *is_copy = true;
                } else {
                    attrs.push(s.clone());
                }
            }
            _ => {
                return Err(ExpansionError::InvalidSyntax(
                    "inductive".to_string(),
                    "Inductive attributes must be symbols".to_string(),
                ))
            }
        }
    }
    Ok(())
}

fn parse_inductive_attrs(items: &[Syntax]) -> Result<(bool, Vec<String>, usize), ExpansionError> {
    let mut is_copy = false;
    let mut attrs = Vec::new();
    let mut name_index = 1;

    match &items[1].kind {
        SyntaxKind::List(list) | SyntaxKind::BracedList(list) => {
            parse_inductive_attr_list(list, &mut is_copy, &mut attrs)?;
            name_index = 2;
        }
        SyntaxKind::Symbol(s) if s == "copy" => {
            is_copy = true;
            name_index = 2;
            if items.len() > 2 {
                if let SyntaxKind::List(list) | SyntaxKind::BracedList(list) = &items[2].kind {
                    parse_inductive_attr_list(list, &mut is_copy, &mut attrs)?;
                    name_index = 3;
                }
            }
        }
        _ => {}
    }

    Ok((is_copy, attrs, name_index))
}

impl<'a> DeclarationParser<'a> {
    pub fn new(expander: &'a mut Expander) -> Self {
        DeclarationParser {
            expander,
            desugarer: Desugarer::new(),
        }
    }

    pub fn parse(
        &mut self,
        syntax_nodes: Vec<Syntax>,
    ) -> Result<Vec<Declaration>, DeclarationParseError> {
        let mut decls = Vec::new();
        for syntax in syntax_nodes {
            if let Some(decl) = self.parse_decl(syntax)? {
                decls.push(decl);
            }
        }
        Ok(decls)
    }

    fn parse_decl(&mut self, syntax: Syntax) -> Result<Option<Declaration>, DeclarationParseError> {
        self.parse_decl_inner(syntax)
    }

    fn parse_decl_inner(
        &mut self,
        syntax: Syntax,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        if let Some(decl) = self.parse_defmacro(&syntax)? {
            return Ok(Some(decl));
        }

        let expanded = match self.expander.expand(syntax)? {
            Some(expanded) => expanded,
            None => return Ok(None),
        };

        if let Some(decl) = self.parse_defmacro(&expanded)? {
            return Ok(Some(decl));
        }

        self.parse_expanded_decl(expanded)
    }

    fn parse_defmacro(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        let items = match &syntax.kind {
            SyntaxKind::List(items) if !items.is_empty() => items,
            _ => return Ok(None),
        };

        let head = match &items[0].kind {
            SyntaxKind::Symbol(s) if s == "defmacro" => s.as_str(),
            _ => return Ok(None),
        };

        if items.len() != 4 {
            return Err(ExpansionError::ArgumentCountMismatch(
                head.to_string(),
                3,
                items.len() - 1,
            )
            .into());
        }
        let name = if let SyntaxKind::Symbol(n) = &items[1].kind {
            n.clone()
        } else {
            return Err(ExpansionError::InvalidSyntax(
                head.to_string(),
                "Name must be a symbol".to_string(),
            )
            .into());
        };
        if is_reserved_macro_name(&name) {
            return Err(ExpansionError::InvalidSyntax(
                head.to_string(),
                format!("'{}' is a reserved macro name", name),
            )
            .into());
        }

        let mut args = Vec::new();
        if let SyntaxKind::List(arg_list) = &items[2].kind {
            for arg in arg_list {
                if let SyntaxKind::Symbol(a) = &arg.kind {
                    args.push(a.clone());
                } else {
                    return Err(ExpansionError::InvalidSyntax(
                        head.to_string(),
                        "Args must be symbols".to_string(),
                    )
                    .into());
                }
            }
        } else {
            return Err(ExpansionError::InvalidSyntax(
                head.to_string(),
                "Arg list expected".to_string(),
            )
            .into());
        }

        let body = items[3].clone();
        self.expander
            .add_macro(name.clone(), args.clone(), body.clone());
        Ok(Some(Declaration::DefMacro { name, args, body }))
    }

    fn parse_expanded_decl(
        &mut self,
        syntax: Syntax,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        match &syntax.kind {
            SyntaxKind::List(items) => {
                if items.is_empty() {
                    return Ok(None);
                }
                if let SyntaxKind::Symbol(s) = &items[0].kind {
                    match s.as_str() {
                        "def" => {
                            self.parse_def_with_transparency(items, "def", Totality::Total, false)
                        }
                        "partial" => self.parse_def_with_transparency(
                            items,
                            "partial",
                            Totality::Partial,
                            false,
                        ),
                        "unsafe" => {
                            if items.len() >= 2 {
                                if let SyntaxKind::Symbol(sym) = &items[1].kind {
                                    if sym == "instance" {
                                        return self.parse_instance_at(
                                            items,
                                            "unsafe instance",
                                            2,
                                            true,
                                        );
                                    }
                                }
                            }
                            self.parse_def_with_transparency(
                                items,
                                "unsafe",
                                Totality::Unsafe,
                                false,
                            )
                        }
                        "noncomputable" => self.parse_def_with_transparency(
                            items,
                            "noncomputable",
                            Totality::Total,
                            true,
                        ),
                        "opaque" => self.parse_def_fixed_transparency(
                            items,
                            "opaque",
                            Totality::Total,
                            Transparency::None,
                            false,
                        ),
                        "transparent" => self.parse_def_fixed_transparency(
                            items,
                            "transparent",
                            Totality::Total,
                            Transparency::Reducible,
                            false,
                        ),
                        "axiom" => {
                            if !(items.len() == 3 || items.len() == 4) {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "axiom".to_string(),
                                    2,
                                    items.len() - 1,
                                )
                                .into());
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
                                                )
                                                .into());
                                            }
                                        }
                                    }
                                    _ => {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "axiom".to_string(),
                                            "Axiom tags must be a symbol or list of symbols"
                                                .to_string(),
                                        )
                                        .into());
                                    }
                                }
                            }

                            let name = if let SyntaxKind::Symbol(n) = &name_syntax.kind {
                                n.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "axiom".to_string(),
                                    "Name must be a symbol".to_string(),
                                )
                                .into());
                            };
                            let ty = self.desugarer.desugar(ty_syntax.clone())?;
                            Ok(Some(Declaration::Axiom { name, ty, tags }))
                        }
                        "module" => {
                            if items.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "module".to_string(),
                                    1,
                                    items.len() - 1,
                                )
                                .into());
                            }
                            let name = if let SyntaxKind::Symbol(name) = &items[1].kind {
                                name.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "module".to_string(),
                                    "Module name must be a symbol".to_string(),
                                )
                                .into());
                            };
                            Ok(Some(Declaration::Module { name }))
                        }
                        "import" => match items.len() {
                            2 => match &items[1].kind {
                                SyntaxKind::Symbol(tag) if tag == "classical" => {
                                    Ok(Some(Declaration::ImportClassical))
                                }
                                SyntaxKind::Symbol(module) => Ok(Some(Declaration::ImportModule {
                                    module: module.clone(),
                                    alias: None,
                                })),
                                _ => Err(ExpansionError::InvalidSyntax(
                                    "import".to_string(),
                                    "Expected 'classical' or a module name".to_string(),
                                )
                                .into()),
                            },
                            4 => {
                                let module = if let SyntaxKind::Symbol(module) = &items[1].kind {
                                    module.clone()
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "import".to_string(),
                                        "Import target must be a module symbol".to_string(),
                                    )
                                    .into());
                                };
                                match &items[2].kind {
                                    SyntaxKind::Symbol(as_kw) if as_kw == "as" => {}
                                    _ => {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "import".to_string(),
                                            "Expected '(import <module> as <alias>)'".to_string(),
                                        )
                                        .into())
                                    }
                                }
                                let alias = if let SyntaxKind::Symbol(alias) = &items[3].kind {
                                    alias.clone()
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "import".to_string(),
                                        "Alias must be a symbol".to_string(),
                                    )
                                    .into());
                                };
                                Ok(Some(Declaration::ImportModule {
                                    module,
                                    alias: Some(alias),
                                }))
                            }
                            _ => Err(ExpansionError::InvalidSyntax(
                                "import".to_string(),
                                "Expected '(import <module>)' or '(import <module> as <alias>)'"
                                    .to_string(),
                            )
                            .into()),
                        },
                        "open" => {
                            if items.len() != 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "open".to_string(),
                                    1,
                                    items.len() - 1,
                                )
                                .into());
                            }
                            let target = if let SyntaxKind::Symbol(target) = &items[1].kind {
                                target.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "open".to_string(),
                                    "Open target must be a symbol".to_string(),
                                )
                                .into());
                            };
                            Ok(Some(Declaration::OpenModule { target }))
                        }
                        "instance" => self.parse_instance_at(items, "instance", 1, false),
                        "inductive" => {
                            if items.len() < 3 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "inductive".to_string(),
                                    2,
                                    items.len() - 1,
                                )
                                .into());
                            }
                            let (is_copy, attrs, name_index) = parse_inductive_attrs(items)?;
                            if items.len() < name_index + 2 {
                                return Err(ExpansionError::ArgumentCountMismatch(
                                    "inductive".to_string(),
                                    2,
                                    items.len() - 1,
                                )
                                .into());
                            }
                            let name_syntax = &items[name_index];
                            let ty_syntax = &items[name_index + 1];
                            let ctor_slice = items.iter().skip(name_index + 2);

                            let name = if let SyntaxKind::Symbol(n) = &name_syntax.kind {
                                n.clone()
                            } else {
                                return Err(ExpansionError::InvalidSyntax(
                                    "inductive".to_string(),
                                    "Name must be a symbol".to_string(),
                                )
                                .into());
                            };
                            let ty = self.desugarer.desugar(ty_syntax.clone())?;

                            let mut ctors = Vec::new();
                            for ctor_spec in ctor_slice {
                                if let SyntaxKind::List(citems) = &ctor_spec.kind {
                                    if citems.len() == 2 {
                                        // (Name Type)
                                        if let SyntaxKind::Symbol(cname) = &citems[0].kind {
                                            let cty = self.desugarer.desugar(citems[1].clone())?;
                                            ctors.push((cname.clone(), cty));
                                        } else {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "inductive ctor".to_string(),
                                                "Expected (Name Type)".to_string(),
                                            )
                                            .into());
                                        }
                                    } else if citems.len() == 3 {
                                        // (Name : Type)
                                        if let SyntaxKind::Symbol(s) = &citems[1].kind {
                                            if s == ":" {
                                                if let SyntaxKind::Symbol(cname) = &citems[0].kind {
                                                    let cty = self
                                                        .desugarer
                                                        .desugar(citems[2].clone())?;
                                                    ctors.push((cname.clone(), cty));
                                                } else {
                                                    return Err(ExpansionError::InvalidSyntax(
                                                        "inductive ctor".to_string(),
                                                        "Expected (Name : Type)".to_string(),
                                                    )
                                                    .into());
                                                }
                                            } else {
                                                // (ctor Name Type)
                                                if let SyntaxKind::Symbol(head) = &citems[0].kind {
                                                    if head == "ctor" {
                                                        if let SyntaxKind::Symbol(cname) =
                                                            &citems[1].kind
                                                        {
                                                            let cty = self
                                                                .desugarer
                                                                .desugar(citems[2].clone())?;
                                                            ctors.push((cname.clone(), cty));
                                                        } else {
                                                            return Err(
                                                                ExpansionError::InvalidSyntax(
                                                                    "inductive ctor".to_string(),
                                                                    "Expected (ctor Name Type)"
                                                                        .to_string(),
                                                                )
                                                                .into(),
                                                            );
                                                        }
                                                    } else {
                                                        return Err(ExpansionError::InvalidSyntax(
                                                            "inductive ctor".to_string(),
                                                            "Expected (Name : Type) or (ctor Name Type)"
                                                                .to_string(),
                                                        )
                                                        .into());
                                                    }
                                                } else {
                                                    return Err(ExpansionError::InvalidSyntax(
                                                        "inductive ctor".to_string(),
                                                        "Expected (Name : Type) or (ctor Name Type)"
                                                            .to_string(),
                                                    )
                                                    .into());
                                                }
                                            }
                                        } else {
                                            return Err(ExpansionError::InvalidSyntax(
                                                "inductive ctor".to_string(),
                                                "Expected (Name : Type) or (ctor Name Type)"
                                                    .to_string(),
                                            )
                                            .into());
                                        }
                                    } else {
                                        return Err(ExpansionError::InvalidSyntax(
                                            "inductive ctor".to_string(),
                                            "Expected (Name Type) or (Name : Type) or (ctor Name Type)"
                                                .to_string(),
                                        )
                                        .into());
                                    }
                                } else {
                                    return Err(ExpansionError::InvalidSyntax(
                                        "inductive ctor".to_string(),
                                        "Expected list".to_string(),
                                    )
                                    .into());
                                }
                            }
                            Ok(Some(Declaration::Inductive {
                                name,
                                ty,
                                ctors,
                                is_copy,
                                attrs,
                            }))
                        }
                        _ => {
                            let term = self.desugarer.desugar(syntax.clone())?;
                            Ok(Some(Declaration::Expr(term)))
                        }
                    }
                } else {
                    let term = self.desugarer.desugar(syntax.clone())?;
                    Ok(Some(Declaration::Expr(term)))
                }
            }
            _ => {
                let term = self.desugarer.desugar(syntax.clone())?;
                Ok(Some(Declaration::Expr(term)))
            }
        }
    }

    fn parse_def_with_transparency(
        &mut self,
        items: &[Syntax],
        head: &str,
        totality: Totality,
        noncomputable: bool,
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
                return Err(ExpansionError::ArgumentCountMismatch(
                    head.to_string(),
                    3,
                    items.len() - 1,
                )
                .into())
            }
        };

        self.parse_def_at(
            items,
            head,
            name_index,
            totality,
            transparency,
            noncomputable,
        )
    }

    fn parse_def_fixed_transparency(
        &mut self,
        items: &[Syntax],
        head: &str,
        totality: Totality,
        transparency: Transparency,
        noncomputable: bool,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        if items.len() != 4 {
            return Err(ExpansionError::ArgumentCountMismatch(
                head.to_string(),
                3,
                items.len() - 1,
            )
            .into());
        }
        self.parse_def_at(items, head, 1, totality, transparency, noncomputable)
    }

    fn parse_instance_at(
        &mut self,
        items: &[Syntax],
        head: &str,
        arg_start: usize,
        is_unsafe: bool,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        let arg_count = items.len().saturating_sub(arg_start);
        if arg_count < 2 {
            return Err(
                ExpansionError::ArgumentCountMismatch(head.to_string(), 2, arg_count).into(),
            );
        }

        let trait_name = match &items[arg_start].kind {
            SyntaxKind::Symbol(name) => name.clone(),
            _ => {
                return Err(ExpansionError::InvalidSyntax(
                    head.to_string(),
                    "Trait name must be a symbol".to_string(),
                )
                .into())
            }
        };

        let head_term = self.desugarer.desugar(items[arg_start + 1].clone())?;
        let mut requirements = Vec::new();
        for req in items.iter().skip(arg_start + 2) {
            requirements.push(self.desugarer.desugar(req.clone())?);
        }

        Ok(Some(Declaration::Instance {
            trait_name,
            head: head_term,
            requirements,
            is_unsafe,
        }))
    }

    fn parse_def_at(
        &mut self,
        items: &[Syntax],
        head: &str,
        name_index: usize,
        totality: Totality,
        transparency: Transparency,
        noncomputable: bool,
    ) -> Result<Option<Declaration>, DeclarationParseError> {
        let name = if let SyntaxKind::Symbol(n) = &items[name_index].kind {
            n.clone()
        } else {
            return Err(ExpansionError::InvalidSyntax(
                head.to_string(),
                "Name must be a symbol".to_string(),
            )
            .into());
        };

        let ty = self.desugarer.desugar(items[name_index + 1].clone())?;
        let val = self.desugarer.desugar(items[name_index + 2].clone())?;
        if totality != Totality::Partial && val.contains_fix() {
            return Err(ExpansionError::InvalidSyntax(
                head.to_string(),
                "fix is only allowed in partial definitions".to_string(),
            )
            .into());
        }

        Ok(Some(Declaration::Def {
            name,
            ty,
            val,
            totality,
            transparency,
            noncomputable,
        }))
    }
}
