use crate::errors::SourceSpan;
use kernel::ast::{FunctionKind, MarkerId, Term, TypeMarker};
use kernel::checker::{whnf, Builtin, Env, TypeError};
use kernel::Transparency;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Clone)]
pub struct AdtId {
    id: u64,
    name: Rc<str>,
    builtin: Option<Builtin>,
}

impl AdtId {
    pub fn new(name: impl AsRef<str>) -> Self {
        Self::with_builtin(name, None)
    }

    pub fn with_builtin(name: impl AsRef<str>, builtin: Option<Builtin>) -> Self {
        let name_ref = name.as_ref();
        AdtId {
            id: stable_hash64("adt", name_ref),
            name: Rc::from(name_ref),
            builtin,
        }
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn is_builtin(&self, builtin: Builtin) -> bool {
        self.builtin == Some(builtin)
    }
}

impl fmt::Debug for AdtId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AdtId({}, {})", self.name, self.id)
    }
}

impl PartialEq for AdtId {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for AdtId {}

impl Hash for AdtId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u64);

impl DefId {
    pub fn new(name: impl AsRef<str>) -> Self {
        DefId(stable_hash64("def", name.as_ref()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CtorId {
    pub adt: AdtId,
    pub index: u32,
}

impl CtorId {
    pub fn new(adt: AdtId, index: usize) -> Self {
        CtorId {
            adt,
            index: index as u32,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AdtLayout {
    pub adt: AdtId,
    pub variants: Vec<VariantLayout>,
    /// The kernel's Copy instances of this inductive, as MIR type templates over the
    /// parameters (`Param(i)`): the ADT is Copy at arguments `args` iff, for some instance,
    /// every requirement is Copy at `args` (docs/spec/ownership_model.md, Copy). Empty when the
    /// inductive has no Copy instance (e.g. it is `affine`).
    pub copy_requirements: Vec<Vec<MirType>>,
}

#[derive(Debug, Clone)]
pub struct VariantLayout {
    pub ctor: CtorId,
    pub fields: Vec<MirType>,
}

impl AdtLayout {
    pub fn field_template(&self, variant: usize, field: usize) -> Option<&MirType> {
        self.variants
            .get(variant)
            .and_then(|layout| layout.fields.get(field))
    }

    pub fn field_type(&self, variant: usize, field: usize, args: &[MirType]) -> Option<MirType> {
        let template = self.field_template(variant, field)?;
        Some(template.substitute_params(args))
    }
}

#[derive(Clone, Default)]
pub struct AdtLayoutRegistry {
    layouts: HashMap<AdtId, AdtLayout>,
}

#[derive(Debug, Clone)]
pub struct IdRegistryError {
    message: String,
    span: Option<SourceSpan>,
}

impl IdRegistryError {
    fn new(message: impl Into<String>, span: Option<SourceSpan>) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }

    pub fn span(&self) -> Option<SourceSpan> {
        self.span
    }
}

impl fmt::Display for IdRegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for IdRegistryError {}

struct SortedAdtLayouts<'a> {
    entries: Vec<(&'a AdtId, &'a AdtLayout)>,
}

impl<'a> fmt::Debug for SortedAdtLayouts<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for (key, value) in &self.entries {
            map.entry(key, value);
        }
        map.finish()
    }
}

impl fmt::Debug for AdtLayoutRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut entries: Vec<_> = self.layouts.iter().collect();
        entries.sort_by(|(a, _), (b, _)| a.name().cmp(b.name()).then_with(|| a.id().cmp(&b.id())));
        f.debug_struct("AdtLayoutRegistry")
            .field("layouts", &SortedAdtLayouts { entries })
            .finish()
    }
}

impl AdtLayoutRegistry {
    pub fn get(&self, adt: &AdtId) -> Option<&AdtLayout> {
        self.layouts.get(adt)
    }

    /// Copy-ness of a MIR type with the inductives' Copy instances available: like
    /// `MirType::is_copy`, except that an ADT is Copy when one of its Copy instances is
    /// satisfied at its arguments (`MirType::is_copy` has no access to the instances and treats
    /// every ADT as non-Copy). A cyclic query is not Copy, as in the kernel.
    pub fn type_is_copy(&self, ty: &MirType) -> bool {
        self.type_is_copy_inner(ty, &mut Vec::new())
    }

    fn type_is_copy_inner(&self, ty: &MirType, stack: &mut Vec<MirType>) -> bool {
        let MirType::Adt(adt, args) = ty else {
            return ty.is_copy();
        };
        if stack.contains(ty) {
            return false;
        }
        let Some(layout) = self.layouts.get(adt) else {
            return false;
        };
        stack.push(ty.clone());
        let result = layout.copy_requirements.iter().any(|requirements| {
            requirements.iter().all(|requirement| {
                self.type_is_copy_inner(&requirement.substitute_params(args), stack)
            })
        });
        stack.pop();
        result
    }

    pub fn field_type(
        &self,
        adt: &AdtId,
        variant: Option<usize>,
        field: usize,
        args: &[MirType],
    ) -> Option<MirType> {
        let layout = self.layouts.get(adt)?;
        let variant = match variant {
            Some(idx) => Some(idx),
            None if layout.variants.len() == 1 => Some(0),
            None => None,
        }?;
        layout.field_type(variant, field, args)
    }
}

#[derive(Debug, Clone)]
pub struct IdRegistry {
    adt_by_name: HashMap<String, AdtId>,
    ctor_arities: HashMap<CtorId, usize>,
    def_by_name: HashMap<String, DefId>,
    builtin_adts: HashMap<Builtin, AdtId>,
    adt_num_params: HashMap<AdtId, usize>,
    /// For each inductive, one flag per uniform parameter: `true` if the parameter is a
    /// type (its binder type is a sort, possibly after a Π-telescope), `false` if it is a
    /// value parameter (e.g. `x : A` in `Eq A x`). Value parameters do not influence the
    /// runtime representation and are lowered to the `Unit` placeholder.
    adt_type_params: HashMap<AdtId, Vec<bool>>,
    /// For each inductive, one MIR type per uniform parameter: the type of a value parameter
    /// (its binder type, with earlier parameters as `Param`), `Unit` for a type parameter. The
    /// value is not part of the runtime representation, but constructors still receive it.
    adt_param_value_types: HashMap<AdtId, Vec<MirType>>,
    adt_layouts: AdtLayoutRegistry,
    indexable_adts: HashSet<AdtId>,
    index_defs: HashSet<DefId>,
    ref_def: Option<DefId>,
    mut_def: Option<DefId>,
    shared_def: Option<DefId>,
    errors: Vec<IdRegistryError>,
}

impl IdRegistry {
    pub fn from_env(env: &Env) -> Self {
        let mut adt_by_name = HashMap::new();
        let mut ctor_arities = HashMap::new();
        let mut builtin_adts = HashMap::new();
        let mut adt_num_params = HashMap::new();
        let mut adt_type_params = HashMap::new();
        let mut indexable_adts = HashSet::new();
        let mut errors = Vec::new();

        let mut inductives: Vec<_> = env.inductives.iter().collect();
        inductives.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (name, decl) in inductives {
            let builtin = if env.is_builtin(Builtin::Nat, name) {
                Some(Builtin::Nat)
            } else if env.is_builtin(Builtin::Bool, name) {
                Some(Builtin::Bool)
            } else if env.is_builtin(Builtin::List, name) {
                Some(Builtin::List)
            } else {
                None
            };

            let adt_id = AdtId::with_builtin(name, builtin.clone());
            adt_by_name.insert(name.clone(), adt_id.clone());
            adt_num_params.insert(adt_id.clone(), decl.num_params);
            adt_type_params.insert(
                adt_id.clone(),
                param_type_flags(env, &decl.ty, decl.num_params),
            );
            if has_marker_checked(
                env,
                &decl.markers,
                TypeMarker::Indexable,
                &format!("inductive '{}'", name),
                &mut errors,
            ) {
                indexable_adts.insert(adt_id.clone());
            }

            if let Some(builtin) = builtin {
                builtin_adts.insert(builtin, adt_id.clone());
            }

            for (idx, ctor) in decl.ctors.iter().enumerate() {
                let arity = ctor_arity(&ctor.ty);
                ctor_arities.insert(CtorId::new(adt_id.clone(), idx), arity);
            }
        }

        let mut def_by_name = HashMap::new();
        for name in env.definitions().keys() {
            def_by_name.insert(name.clone(), DefId::new(name));
        }

        let mut index_defs = HashSet::new();
        for name in ["index_vec_dyn", "index_slice", "index_array"] {
            if let Some(def_id) = def_by_name.get(name).copied() {
                index_defs.insert(def_id);
            }
        }

        let ref_def = def_by_name.get("Ref").copied();
        let mut_def = def_by_name.get("Mut").copied();
        let shared_def = def_by_name.get("Shared").copied();

        let mut registry = IdRegistry {
            adt_by_name,
            ctor_arities,
            def_by_name,
            builtin_adts,
            adt_num_params,
            adt_type_params,
            adt_param_value_types: HashMap::new(),
            adt_layouts: AdtLayoutRegistry::default(),
            indexable_adts,
            index_defs,
            ref_def,
            mut_def,
            shared_def,
            errors: Vec::new(),
        };
        registry.build_layouts(env, &mut errors);
        registry.build_param_value_types(env, &mut errors);
        registry.errors = errors;
        registry
    }

    /// The MIR type of the argument a constructor of `adt` receives for parameter `idx`: the
    /// parameter's type for a value parameter (e.g. `Nat` for `k` in `VSplit A k`), `Unit` for
    /// a type parameter (types are erased). `None` for unknown ADTs or indices.
    pub fn adt_param_value_type(&self, adt: &AdtId, idx: usize) -> Option<&MirType> {
        self.adt_param_value_types
            .get(adt)
            .and_then(|types| types.get(idx))
    }

    pub fn adt_id(&self, name: &str) -> Option<AdtId> {
        self.adt_by_name.get(name).cloned()
    }

    pub fn ctor_id(&self, name: &str, index: usize) -> Option<CtorId> {
        let adt = self.adt_id(name)?;
        let ctor = CtorId::new(adt, index);
        if self.ctor_arities.contains_key(&ctor) {
            Some(ctor)
        } else {
            None
        }
    }

    pub fn ctor_arity(&self, ctor: &CtorId) -> Option<usize> {
        self.ctor_arities.get(ctor).copied()
    }

    pub fn def_id(&self, name: &str) -> Option<DefId> {
        self.def_by_name.get(name).copied()
    }

    pub fn builtin_adt(&self, builtin: Builtin) -> Option<AdtId> {
        self.builtin_adts.get(&builtin).cloned()
    }

    pub fn adt_num_params(&self, adt: &AdtId) -> Option<usize> {
        self.adt_num_params.get(adt).copied()
    }

    /// Whether parameter `idx` of `adt` is a type parameter (see `adt_type_params`).
    /// Unknown ADTs and out-of-range indices are treated as type parameters.
    pub fn adt_param_is_type(&self, adt: &AdtId, idx: usize) -> bool {
        self.adt_type_params
            .get(adt)
            .and_then(|flags| flags.get(idx))
            .copied()
            .unwrap_or(true)
    }

    pub fn adt_layouts(&self) -> &AdtLayoutRegistry {
        &self.adt_layouts
    }

    pub fn adt_layout(&self, adt: &AdtId) -> Option<&AdtLayout> {
        self.adt_layouts.get(adt)
    }

    pub fn is_indexable_adt(&self, adt: &AdtId) -> bool {
        self.indexable_adts.contains(adt)
    }

    pub fn is_index_def(&self, def_id: DefId) -> bool {
        self.index_defs.contains(&def_id)
    }

    pub fn ref_def(&self) -> Option<DefId> {
        self.ref_def
    }

    pub fn mut_def(&self) -> Option<DefId> {
        self.mut_def
    }

    pub fn shared_def(&self) -> Option<DefId> {
        self.shared_def
    }

    pub fn errors(&self) -> &[IdRegistryError] {
        &self.errors
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    fn build_param_value_types(&mut self, env: &Env, errors: &mut Vec<IdRegistryError>) {
        let mut param_value_types = HashMap::new();
        let mut inductives: Vec<_> = env.inductives.iter().collect();
        inductives.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (name, decl) in inductives {
            let adt_id = self
                .adt_by_name
                .get(name)
                .cloned()
                .unwrap_or_else(|| AdtId::new(name));
            let mut types = Vec::with_capacity(decl.num_params);
            let mut current = decl.ty.clone();
            for idx in 0..decl.num_params {
                let Term::Pi(dom, body, _, _) = &*current else {
                    break;
                };
                if self.adt_param_is_type(&adt_id, idx) {
                    types.push(MirType::Unit);
                } else {
                    // The binder's type is in the scope of the `idx` parameters before it.
                    types.push(lower_type_template(dom, idx, 0, env, self, errors));
                }
                current = body.clone();
            }
            param_value_types.insert(adt_id, types);
        }
        self.adt_param_value_types = param_value_types;
    }

    fn build_layouts(&mut self, env: &Env, errors: &mut Vec<IdRegistryError>) {
        let mut layouts = HashMap::new();
        let mut inductives: Vec<_> = env.inductives.iter().collect();
        inductives.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (name, decl) in inductives {
            let adt_id = self
                .adt_by_name
                .get(name)
                .cloned()
                .unwrap_or_else(|| AdtId::new(name));
            let mut variants = Vec::new();
            for (ctor_idx, ctor) in decl.ctors.iter().enumerate() {
                let fields = ctor_field_templates(&ctor.ty, decl.num_params, env, self, errors);
                variants.push(VariantLayout {
                    ctor: CtorId::new(adt_id.clone(), ctor_idx),
                    fields,
                });
            }
            // Copy instances whose requirements mention only the parameters (derived
            // instances always do; an explicit instance over the indices too is skipped, so MIR
            // stays conservative for it). Lowering problems of a requirement are not layout
            // errors: an unrepresentable requirement is `Opaque`, which is never Copy.
            let mut copy_requirements = Vec::new();
            for instance in env.copy_instances().get(name).into_iter().flatten() {
                if instance.param_count != decl.num_params {
                    continue;
                }
                let mut scratch = Vec::new();
                copy_requirements.push(
                    instance
                        .requirements
                        .iter()
                        .map(|req| {
                            lower_type_template(req, decl.num_params, 0, env, self, &mut scratch)
                        })
                        .collect(),
                );
            }
            layouts.insert(
                adt_id.clone(),
                AdtLayout {
                    adt: adt_id,
                    variants,
                    copy_requirements,
                },
            );
        }
        self.adt_layouts = AdtLayoutRegistry { layouts };
    }
}

/// One flag per uniform parameter of an inductive whose type is `ind_ty`: `true` when the
/// parameter's binder type is a sort or a Π-telescope ending in a sort (a type or a type
/// family), `false` for a value parameter.
fn param_type_flags(env: &Env, ind_ty: &Rc<Term>, num_params: usize) -> Vec<bool> {
    let mut flags = Vec::with_capacity(num_params);
    let mut current = ind_ty.clone();
    while flags.len() < num_params {
        let Term::Pi(dom, body, _, _) = &*current else {
            break;
        };
        flags.push(binder_is_type_like(env, dom));
        current = body.clone();
    }
    while flags.len() < num_params {
        flags.push(true);
    }
    flags
}

fn binder_is_type_like(env: &Env, dom: &Rc<Term>) -> bool {
    let mut current = match whnf(env, dom.clone(), Transparency::Reducible) {
        Ok(norm) => norm,
        // Keep the historical behaviour (lower the argument as a type) if normalisation fails.
        Err(_) => return true,
    };
    loop {
        match &*current {
            Term::Sort(_) => return true,
            Term::Pi(_, body, _, _) => {
                current = match whnf(env, body.clone(), Transparency::Reducible) {
                    Ok(norm) => norm,
                    Err(_) => return true,
                };
            }
            _ => return false,
        }
    }
}

fn ctor_arity(ty: &Rc<Term>) -> usize {
    let mut arity = 0;
    let mut current = ty;
    while let Term::Pi(_, body, _, _) = &**current {
        arity += 1;
        current = body;
    }
    arity
}

fn stable_hash64(tag: &str, name: &str) -> u64 {
    const FNV_OFFSET: u64 = 14695981039346656037;
    const FNV_PRIME: u64 = 1099511628211;

    let mut hash = FNV_OFFSET;
    for b in tag.as_bytes() {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash ^= b':' as u64;
    hash = hash.wrapping_mul(FNV_PRIME);
    for b in name.as_bytes() {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

fn ctor_field_templates(
    ctor_ty: &Rc<Term>,
    num_params: usize,
    env: &Env,
    ids: &IdRegistry,
    errors: &mut Vec<IdRegistryError>,
) -> Vec<MirType> {
    let mut fields = Vec::new();
    let mut current = ctor_ty.clone();
    let mut binder_idx = 0usize;

    while let Term::Pi(dom, body, _, _) = &*current {
        if binder_idx >= num_params {
            let field_idx = binder_idx - num_params;
            let field_ty = lower_type_template(dom, num_params, field_idx, env, ids, errors);
            fields.push(field_ty);
        }
        current = body.clone();
        binder_idx += 1;
    }

    fields
}

fn lower_type_template(
    term: &Rc<Term>,
    num_params: usize,
    non_param_binders: usize,
    env: &Env,
    ids: &IdRegistry,
    errors: &mut Vec<IdRegistryError>,
) -> MirType {
    let term_norm = match whnf(env, term.clone(), Transparency::Reducible) {
        Ok(norm) => norm,
        Err(err) => {
            let error = IdRegistryError::new(
                format!(
                    "Failed to normalize type while building MIR layout template: {}",
                    err
                ),
                None,
            );
            if !errors
                .iter()
                .any(|existing| existing.message == error.message)
            {
                errors.push(error);
            }
            return MirType::Opaque {
                reason: opaque_reason(term),
            };
        }
    };

    if let Some((mutability, inner)) = parse_ref_type(&term_norm, ids) {
        let inner_ty = lower_type_template(&inner, num_params, non_param_binders, env, ids, errors);
        return MirType::Ref(Region::STATIC, Box::new(inner_ty), mutability);
    }

    if let Some((kind, inner)) = parse_interior_mutability_type(&term_norm, env, errors) {
        let inner_ty = lower_type_template(&inner, num_params, non_param_binders, env, ids, errors);
        return MirType::InteriorMutable(Box::new(inner_ty), kind);
    }

    match &*term_norm {
        Term::Sort(_) => MirType::Unit,
        Term::Var(idx) => {
            if *idx < non_param_binders {
                MirType::Unit
            } else {
                let param_rev = idx - non_param_binders;
                if param_rev >= num_params {
                    MirType::Unit
                } else {
                    let param_idx = num_params - 1 - param_rev;
                    MirType::Param(param_idx)
                }
            }
        }
        Term::Pi(dom, body, _, kind) => {
            let arg = lower_type_template(dom, num_params, non_param_binders, env, ids, errors);
            let ret =
                lower_type_template(body, num_params, non_param_binders + 1, env, ids, errors);
            MirType::Fn(*kind, Vec::new(), vec![arg], Box::new(ret))
        }
        Term::Ind(name, _) => {
            lower_inductive_template(name, &[], num_params, non_param_binders, env, ids, errors)
        }
        Term::App(_, _, _) => {
            let (head, args) = collect_app_spine(&term_norm);
            match &*head {
                Term::Ind(name, _) => lower_inductive_template(
                    name,
                    &args,
                    num_params,
                    non_param_binders,
                    env,
                    ids,
                    errors,
                ),
                _ => MirType::Opaque {
                    reason: opaque_reason(&term_norm),
                },
            }
        }
        _ => MirType::Opaque {
            reason: opaque_reason(&term_norm),
        },
    }
}

fn opaque_reason(term: &Rc<Term>) -> String {
    match &**term {
        Term::Const(name, _) => format!("const {}", name),
        Term::Var(idx) => format!("var {}", idx),
        Term::App(_, _, _) => {
            let (head, _) = collect_app_spine(term);
            match &*head {
                Term::Const(name, _) => format!("app {}", name),
                Term::Ind(name, _) => format!("app ind {}", name),
                _ => STUCK_TYPE_REASON.to_string(),
            }
        }
        Term::Pi(_, _, _, _) => "pi".to_string(),
        Term::Rec(name, _) => format!("rec {}", name),
        Term::Ctor(name, _, _) => format!("ctor {}", name),
        _ => "unsupported".to_string(),
    }
}

fn lower_inductive_template(
    name: &str,
    args: &[Rc<Term>],
    num_params: usize,
    non_param_binders: usize,
    env: &Env,
    ids: &IdRegistry,
    errors: &mut Vec<IdRegistryError>,
) -> MirType {
    let adt_id = ids.adt_id(name).unwrap_or_else(|| AdtId::new(name));

    if adt_id.is_builtin(Builtin::Nat) {
        return MirType::Nat;
    }
    if adt_id.is_builtin(Builtin::Bool) {
        return MirType::Bool;
    }

    let param_count = ids
        .adt_num_params(&adt_id)
        .or_else(|| env.inductives.get(name).map(|decl| decl.num_params))
        .unwrap_or(args.len());

    // MIR types describe runtime representations: index arguments are erased and value
    // parameters become the `Unit` placeholder (see docs/spec/mir/typing.md).
    let mut kept_args = Vec::new();
    for (idx, arg) in args.iter().enumerate().take(param_count) {
        if ids.adt_param_is_type(&adt_id, idx) {
            kept_args.push(lower_type_template(
                arg,
                num_params,
                non_param_binders,
                env,
                ids,
                errors,
            ));
        } else {
            kept_args.push(MirType::Unit);
        }
    }

    MirType::Adt(adt_id, kept_args)
}

fn collect_app_spine(term: &Rc<Term>) -> (Rc<Term>, Vec<Rc<Term>>) {
    let mut args = Vec::new();
    let mut current = term.clone();

    while let Term::App(f, a, _) = &*current {
        args.push(a.clone());
        current = f.clone();
    }

    args.reverse();
    (current, args)
}

fn parse_ref_type(term: &Rc<Term>, ids: &IdRegistry) -> Option<(Mutability, Rc<Term>)> {
    let ref_def = ids.ref_def()?;
    let mut_def = ids.mut_def()?;
    let shared_def = ids.shared_def()?;

    if let Term::App(f1, inner_ty, _) = &**term {
        if let Term::App(ref_const, kind_node, _) = &**f1 {
            let ref_id = def_id_for_const(ref_const, ids)?;
            if ref_id != ref_def {
                return None;
            }

            let kind_id = def_id_for_const(kind_node, ids)?;
            if kind_id == mut_def {
                return Some((Mutability::Mut, inner_ty.clone()));
            }
            if kind_id == shared_def {
                return Some((Mutability::Not, inner_ty.clone()));
            }
        }
    }
    None
}

fn def_id_for_const(term: &Rc<Term>, ids: &IdRegistry) -> Option<DefId> {
    if let Term::Const(name, _) = &**term {
        ids.def_id(name)
    } else {
        None
    }
}

fn parse_interior_mutability_type(
    term: &Rc<Term>,
    env: &Env,
    errors: &mut Vec<IdRegistryError>,
) -> Option<(IMKind, Rc<Term>)> {
    if let Term::App(f, inner_ty, _) = &**term {
        if let Term::Ind(name, _) = &**f {
            if let Some(decl) = env.inductives.get(name) {
                if let Some(kind) = interior_mutability_kind(env, &decl.markers, name, errors) {
                    return Some((kind, inner_ty.clone()));
                }
            }
        }
    }
    None
}

fn interior_mutability_kind(
    env: &Env,
    markers: &[MarkerId],
    ind_name: &str,
    errors: &mut Vec<IdRegistryError>,
) -> Option<IMKind> {
    let context = format!("interior mutability markers for '{}'", ind_name);
    let mut has = |marker| has_marker_checked(env, markers, marker, &context, errors);

    if has(TypeMarker::MayPanicOnBorrowViolation) {
        return Some(IMKind::RefCell);
    }
    if has(TypeMarker::AtomicPrimitive) {
        return Some(IMKind::Atomic);
    }
    if has(TypeMarker::ConcurrencyPrimitive) {
        return Some(IMKind::Mutex);
    }

    None
}

fn has_marker_checked(
    env: &Env,
    markers: &[MarkerId],
    marker: TypeMarker,
    context: &str,
    errors: &mut Vec<IdRegistryError>,
) -> bool {
    match env.has_marker(markers, marker) {
        Ok(value) => value,
        Err(err) => {
            let error = marker_error(context, err);
            if !errors
                .iter()
                .any(|existing| existing.message == error.message)
            {
                errors.push(error);
            }
            false
        }
    }
}

fn marker_error(context: &str, err: TypeError) -> IdRegistryError {
    IdRegistryError::new(
        format!(
            "Marker registry error while processing {}: {}",
            context, err
        ),
        None,
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Region(pub usize);

impl Region {
    pub const STATIC: Region = Region(0); // Reserve 0 for static/global?
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Not,
    Mut,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum MirType {
    Unit,
    Bool,
    Nat,
    /// Runtime type exists but could not be lowered safely (non-Copy).
    Opaque {
        reason: String,
    },
    /// Inductive type (AdtId, Generic Args): one argument per uniform parameter of the
    /// inductive. MIR types are runtime representation types, so index arguments of an
    /// indexed family are erased (`Vec A n` and `Vec A m` are the same MIR type) and value
    /// (non-type) parameters are represented by `Unit`. Index/value-level typing is the
    /// kernel's responsibility; see docs/spec/mir/typing.md.
    Adt(AdtId, Vec<MirType>),
    /// Reference: &'region mut? T
    Ref(Region, Box<MirType>, Mutability),
    /// Function / Closure: kind <region params> [Args] -> Ret
    /// Region params are ordered by first appearance from lifetime labels or positional refs.
    Fn(FunctionKind, Vec<Region>, Vec<MirType>, Box<MirType>),
    /// Non-capturing function item (copyable).
    FnItem(DefId, FunctionKind, Vec<Region>, Vec<MirType>, Box<MirType>),
    /// Closure value (captures or partial application), not copyable by default.
    /// Carries an explicit self-borrow region parameter used to tie returned references
    /// to the borrow of the closure value.
    Closure(
        FunctionKind,
        Region,
        Vec<Region>,
        Vec<MirType>,
        Box<MirType>,
    ),
    /// Raw pointer (for unsafe/primitives)
    RawPtr(Box<MirType>, Mutability),
    /// Interior Mutability wrapper (RefCell, Mutex, Atomic)
    InteriorMutable(Box<MirType>, IMKind),
    /// Generic type parameter placeholder (for layout templates)
    Param(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IMKind {
    RefCell, // Panics on dynamic borrow violation
    Mutex,   // Blocks or waits, safe for concurrency
    Atomic,  // Hardware atomics
}

/// `Opaque` reason of a *stuck* type: a type whose weak head normal form is an application
/// whose head is neither an inductive type nor a constant -- a type-family variable applied to
/// arguments (`P y`), or a recursor blocked on an unknown major premise, such as the large
/// elimination `rec Nat (λ _. Type) Unit (λ _ _. A) n` for an unknown `n`. Unlike an opaque
/// nominal type (an axiom type, reason `const ...`/`app ...`), a stuck type is equal to an
/// ordinary type for every instantiation of its variables, and values of it are represented
/// uniformly at run time; see docs/spec/mir/typing.md, "Types Computed at Run Time".
pub const STUCK_TYPE_REASON: &str = "app";

impl MirType {
    /// Whether this is the MIR type of a stuck type ([`STUCK_TYPE_REASON`]).
    pub fn is_stuck_type(&self) -> bool {
        matches!(self, MirType::Opaque { reason } if reason == STUCK_TYPE_REASON)
    }

    pub fn is_copy(&self) -> bool {
        match self {
            MirType::Unit | MirType::Bool | MirType::Nat => true,
            MirType::Opaque { .. } => false,
            MirType::Ref(_, _, Mutability::Not) => true, // &T is Copy
            MirType::Ref(_, _, Mutability::Mut) => false, // &mut T is not Copy
            MirType::RawPtr(_, _) => true,
            MirType::Adt(_, _) => false, // Conservative default, needs lookup
            MirType::Fn(_, _, _, _) => false, // Copy-ness is derived during lowering.
            MirType::FnItem(_, _, _, _, _) => true,
            MirType::Closure(_, _, _, _, _) => false,
            MirType::InteriorMutable(_, _) => false, // Usually not Copy (RefCell/Mutex are not)
            MirType::Param(_) => false,
        }
    }

    pub fn substitute_params(&self, params: &[MirType]) -> MirType {
        match self {
            MirType::Param(idx) => params.get(*idx).cloned().unwrap_or(MirType::Unit),
            MirType::Adt(id, args) => MirType::Adt(
                id.clone(),
                args.iter()
                    .map(|arg| arg.substitute_params(params))
                    .collect(),
            ),
            MirType::Ref(region, inner, mutability) => MirType::Ref(
                *region,
                Box::new(inner.substitute_params(params)),
                *mutability,
            ),
            MirType::Fn(kind, region_params, args, ret) => MirType::Fn(
                *kind,
                region_params.clone(),
                args.iter()
                    .map(|arg| arg.substitute_params(params))
                    .collect(),
                Box::new(ret.substitute_params(params)),
            ),
            MirType::FnItem(def_id, kind, region_params, args, ret) => MirType::FnItem(
                *def_id,
                *kind,
                region_params.clone(),
                args.iter()
                    .map(|arg| arg.substitute_params(params))
                    .collect(),
                Box::new(ret.substitute_params(params)),
            ),
            MirType::Closure(kind, self_region, region_params, args, ret) => MirType::Closure(
                *kind,
                *self_region,
                region_params.clone(),
                args.iter()
                    .map(|arg| arg.substitute_params(params))
                    .collect(),
                Box::new(ret.substitute_params(params)),
            ),
            MirType::RawPtr(inner, mutability) => {
                MirType::RawPtr(Box::new(inner.substitute_params(params)), *mutability)
            }
            MirType::InteriorMutable(inner, kind) => {
                MirType::InteriorMutable(Box::new(inner.substitute_params(params)), *kind)
            }
            MirType::Opaque { reason } => MirType::Opaque {
                reason: reason.clone(),
            },
            other => other.clone(),
        }
    }
}

impl fmt::Debug for MirType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MirType::Unit => write!(f, "Unit"),
            MirType::Bool => write!(f, "Bool"),
            MirType::Nat => write!(f, "Nat"),
            MirType::Opaque { reason } => f.debug_tuple("Opaque").field(reason).finish(),
            MirType::Adt(adt_id, args) => f.debug_tuple("Adt").field(adt_id).field(args).finish(),
            MirType::Ref(region, inner, mutability) => f
                .debug_tuple("Ref")
                .field(region)
                .field(inner)
                .field(mutability)
                .finish(),
            MirType::Fn(kind, region_params, args, ret) => match kind {
                FunctionKind::Fn => f
                    .debug_tuple("Fn")
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
                FunctionKind::FnMut => f
                    .debug_tuple("FnMut")
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
                FunctionKind::FnOnce => f
                    .debug_tuple("FnOnce")
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
            },
            MirType::FnItem(def_id, kind, region_params, args, ret) => match kind {
                FunctionKind::Fn => f
                    .debug_tuple("FnItem")
                    .field(def_id)
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
                FunctionKind::FnMut => f
                    .debug_tuple("FnItemMut")
                    .field(def_id)
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
                FunctionKind::FnOnce => f
                    .debug_tuple("FnItemOnce")
                    .field(def_id)
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
            },
            MirType::Closure(kind, self_region, region_params, args, ret) => match kind {
                FunctionKind::Fn => f
                    .debug_tuple("Closure")
                    .field(self_region)
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
                FunctionKind::FnMut => f
                    .debug_tuple("ClosureMut")
                    .field(self_region)
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
                FunctionKind::FnOnce => f
                    .debug_tuple("ClosureOnce")
                    .field(self_region)
                    .field(region_params)
                    .field(args)
                    .field(ret)
                    .finish(),
            },
            MirType::RawPtr(inner, mutability) => f
                .debug_tuple("RawPtr")
                .field(inner)
                .field(mutability)
                .finish(),
            MirType::InteriorMutable(inner, kind) => f
                .debug_tuple("InteriorMutable")
                .field(inner)
                .field(kind)
                .finish(),
            MirType::Param(idx) => f.debug_tuple("Param").field(idx).finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel::ast::{marker_def_id, InductiveDecl, Level, Term, TypeMarker};

    #[test]
    fn id_registry_collects_marker_registry_errors() {
        let mut env = Env::new();
        let sort1 = Term::sort(Level::Succ(Box::new(Level::Zero)));
        let mut decl = InductiveDecl::new("IndexableThing".to_string(), sort1, vec![]);
        decl.markers = vec![marker_def_id(TypeMarker::Indexable)];
        env.inductives.insert(decl.name.clone(), decl);

        let ids = IdRegistry::from_env(&env);
        assert!(ids.has_errors(), "expected marker registry error");
        assert!(
            ids.errors()
                .iter()
                .any(|e| e.to_string().contains("Marker registry error")),
            "expected marker registry error details, got {:?}",
            ids.errors()
        );
    }

    /// MIR Copy-ness of ADTs follows the kernel's Copy instances: a `List Nat` field of an
    /// `affine` value may be copied out of it (case study B's channel log, bug W_B_protocol_1),
    /// a `List Tok` with `Tok` affine may not, and the affine type itself is never Copy.
    #[test]
    fn adt_copy_follows_kernel_copy_instances() {
        use kernel::ast::{marker_name, AxiomTag, BinderInfo, Constructor, Definition};
        let mut env = Env::new();
        let sort1 = Term::sort(Level::Succ(Box::new(Level::Zero)));
        env.set_allow_reserved_primitives(true);
        for marker in [
            TypeMarker::InteriorMutable,
            TypeMarker::MayPanicOnBorrowViolation,
            TypeMarker::ConcurrencyPrimitive,
            TypeMarker::AtomicPrimitive,
            TypeMarker::Indexable,
        ] {
            env.add_definition(Definition::axiom_with_tags(
                marker_name(marker).to_string(),
                sort1.clone(),
                vec![AxiomTag::Unsafe],
            ))
            .expect("marker definition");
        }
        env.set_allow_reserved_primitives(false);
        env.init_marker_registry().expect("marker registry");
        env.add_inductive(InductiveDecl::new(
            "N".to_string(),
            sort1.clone(),
            vec![
                Constructor {
                    name: "z".to_string(),
                    ty: Term::ind("N".to_string()),
                },
                Constructor {
                    name: "s".to_string(),
                    ty: Term::pi(
                        Term::ind("N".to_string()),
                        Term::ind("N".to_string()),
                        BinderInfo::Default,
                    ),
                },
            ],
        ))
        .expect("add N");
        let mut tok = InductiveDecl::new(
            "Tok".to_string(),
            sort1.clone(),
            vec![Constructor {
                name: "mk_tok".to_string(),
                ty: Term::ind("Tok".to_string()),
            }],
        );
        tok.markers = vec![marker_def_id(TypeMarker::Affine)];
        env.add_inductive(tok).expect("add Tok");
        // inductive L (A : Type) : Type | lnil | lcons (h : A) (t : L A)
        let l_of = |a: Rc<Term>| Term::app(Term::ind("L".to_string()), a);
        env.add_inductive(InductiveDecl::new(
            "L".to_string(),
            Term::pi(sort1.clone(), sort1.clone(), BinderInfo::Default),
            vec![
                Constructor {
                    name: "lnil".to_string(),
                    ty: Term::pi(sort1.clone(), l_of(Term::var(0)), BinderInfo::Implicit),
                },
                Constructor {
                    name: "lcons".to_string(),
                    ty: Term::pi(
                        sort1.clone(),
                        Term::pi(
                            Term::var(0),
                            Term::pi(l_of(Term::var(1)), l_of(Term::var(2)), BinderInfo::Default),
                            BinderInfo::Default,
                        ),
                        BinderInfo::Implicit,
                    ),
                },
            ],
        ))
        .expect("add L");

        let ids = IdRegistry::from_env(&env);
        let layouts = ids.adt_layouts();
        let n = MirType::Adt(ids.adt_id("N").expect("N"), vec![]);
        let tok = MirType::Adt(ids.adt_id("Tok").expect("Tok"), vec![]);
        let l = ids.adt_id("L").expect("L");
        assert!(
            layouts.type_is_copy(&n),
            "a field-free-or-Copy-fields type is Copy"
        );
        assert!(!layouts.type_is_copy(&tok), "an affine type is not Copy");
        assert!(layouts.type_is_copy(&MirType::Adt(l.clone(), vec![n.clone()])));
        assert!(!layouts.type_is_copy(&MirType::Adt(l.clone(), vec![tok])));
        assert!(!layouts.type_is_copy(&MirType::Adt(l, vec![MirType::Param(0)])));
        assert!(!n.is_copy(), "MirType::is_copy alone stays conservative");
    }

    #[test]
    fn interior_mutability_kind_records_marker_registry_error() {
        let env = Env::new();
        let markers = vec![marker_def_id(TypeMarker::MayPanicOnBorrowViolation)];
        let mut errors = Vec::new();
        let kind = interior_mutability_kind(&env, &markers, "Cell", &mut errors);

        assert!(kind.is_none(), "expected missing interior mutability kind");
        assert_eq!(errors.len(), 1, "expected one marker registry error");
        assert!(
            errors[0].to_string().contains("Marker registry error"),
            "unexpected error: {:?}",
            errors[0]
        );
    }
}
