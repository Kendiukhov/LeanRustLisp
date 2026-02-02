    fn expand_quasiquote(&mut self, syntax: &Syntax) -> Result<Option<Syntax>, ExpansionError> {
        match &syntax.kind {
            SyntaxKind::List(list) => {
                if !list.is_empty() {
                    if let SyntaxKind::Symbol(s) = &list[0].kind {
                         if s == "unquote" {
                             if list.len() != 2 { return Err(ExpansionError::TransformationError); }
                             // Expand the unquoted expression normally
                             let expanded = self.expand_all_macros(list[1].clone())?;
                             return Ok(expanded);
                         }
                         if s == "unquote-splicing" {
                             // Splicing not allowed at top level of quasiquote effectively? 
                             // Or rather, we need to handle it in the list construction loop.
                             // For now return error or identity if not in list context?
                             return Err(ExpansionError::TransformationError);
                         }
                    }
                }

                // Normal list in quasiquote: recursively process
                let mut new_list = Vec::new();
                for item in list {
                    // Check for splicing
                     match &item.kind {
                         SyntaxKind::List(sub_list) if !sub_list.is_empty() => {
                             if let SyntaxKind::Symbol(s) = &sub_list[0].kind {
                                 if s == "unquote-splicing" {
                                     if sub_list.len() != 2 { return Err(ExpansionError::TransformationError); }
                                     let expanded_list_expr = self.expand_all_macros(sub_list[1].clone())?;
                                     // We expect the result to be a List syntax that we splice in.
                                     // But distinct from runtime eval, macro expansion happens at compile time.
                                     // If the unquoted expression expands to a List Syntax, we splice its elements.
                                     if let Some(syn) = expanded_list_expr {
                                         if let SyntaxKind::List(inner_items) = syn.kind {
                                             new_list.extend(inner_items);
                                         } else {
                                              // If it's not a list literal, we can't splice at compile time?
                                              // Or is this constructing code that splices at runtime?
                                              // The task is to implement Lisp-style macros (syntax->syntax).
                                              // So if (unquote-splicing (list a b)) -> a b in the syntax object.
                                              // But unquote runs *expansion*, not *evaluation* (unless macro eval capabilities exist).
                                              // Wait, `quasiquote` typically means "construct syntax object".
                                              // In standard Lisp: `(1 ,(+ 1 1)) -> (1 2).
                                              // But here, unquote replaces with the *result of expansion*?
                                              // Use-case: (defmacro m (x) `(print ,x)) -> (print <x-syntax>)
                                              // So unquote just effectively "escapes" the quasiquote to put the variable back.
                                              new_list.push(syn);
                                         }
                                     }
                                     continue;
                                 }
                             }
                         }
                         _ => {}
                     }
                     
                     // Not splicing
                     if let Some(res) = self.expand_quasiquote(item)? {
                         new_list.push(res);
                     }
                }
                
                Ok(Some(Syntax { kind: SyntaxKind::List(new_list), ..syntax.clone() }))
            },
            _ => Ok(Some(syntax.clone())) // Symbols, Ints, etc are self-quoted
        }
    }
