use crate::types::{AdtId, AdtLayoutRegistry, CtorId, IMKind, IdRegistry, MirType, Mutability};
use crate::{
    Body, BorrowKind, CallOperand, Constant, Literal, Operand, Place, PlaceElem, RuntimeCheckKind,
    Rvalue, Statement, Terminator,
};
use kernel::ast::{Level, Term};
use kernel::checker::{Builtin, Env};
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum TypedCodegenReason {
    UnsupportedFnMut,
    UnsupportedNonUnaryFunction,
    UnsupportedCallOperand,
    UnsupportedProjectionAssignment,
    UnsupportedPlaceProjection,
    UnsupportedClosureEnvProjection,
    UnsupportedClosureType,
    UnsupportedFixpointType,
    UnsupportedPolymorphicFunctionValue,
    InternalInvariant,
}

impl TypedCodegenReason {
    pub fn code(self) -> &'static str {
        match self {
            TypedCodegenReason::UnsupportedFnMut => "TB001",
            TypedCodegenReason::UnsupportedNonUnaryFunction => "TB002",
            TypedCodegenReason::UnsupportedCallOperand => "TB003",
            TypedCodegenReason::UnsupportedProjectionAssignment => "TB004",
            TypedCodegenReason::UnsupportedPlaceProjection => "TB005",
            TypedCodegenReason::UnsupportedClosureEnvProjection => "TB006",
            TypedCodegenReason::UnsupportedClosureType => "TB007",
            TypedCodegenReason::UnsupportedFixpointType => "TB008",
            TypedCodegenReason::UnsupportedPolymorphicFunctionValue => "TB009",
            TypedCodegenReason::InternalInvariant => "TB900",
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypedCodegenError {
    pub reason: TypedCodegenReason,
    pub message: String,
}

impl TypedCodegenError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            reason: TypedCodegenReason::InternalInvariant,
            message: message.into(),
        }
    }

    pub fn unsupported(reason: TypedCodegenReason, message: impl Into<String>) -> Self {
        Self {
            reason,
            message: message.into(),
        }
    }

    pub fn with_context(self, context: impl AsRef<str>) -> Self {
        Self {
            reason: self.reason,
            message: format!("{}: {}", context.as_ref(), self.message),
        }
    }

    pub fn code(&self) -> &'static str {
        self.reason.code()
    }
}

impl std::fmt::Display for TypedCodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}", self.code(), self.message)
    }
}

impl std::error::Error for TypedCodegenError {}

#[derive(Debug, Clone)]
pub struct TypedBody {
    pub name: String,
    pub body: Body,
    pub closure_base: usize,
}

#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub defs: Vec<TypedBody>,
    pub closures: Vec<TypedBody>,
    pub main_name: Option<String>,
}

pub fn codegen_program(
    env: &Env,
    ids: &IdRegistry,
    program: &TypedProgram,
) -> Result<String, TypedCodegenError> {
    let mut ctx = CodegenContext::new(env, ids)?;
    ctx.check_program_supported(program)?;

    let mut items = Vec::new();
    items.push(Item::CrateAttr(
        "allow(dead_code, unused_variables, unused_parens, unused_mut, unreachable_patterns, non_snake_case, non_camel_case_types)".to_string(),
    ));
    items.push(Item::Use("std::rc::Rc".to_string()));
    items.extend(ctx.emit_callable_runtime_items());
    items.extend(ctx.emit_adts()?);
    items.extend(ctx.emit_index_runtime_impls()?);
    items.extend(ctx.emit_text_io_runtime_items()?);
    items.extend(ctx.emit_int_runtime_items()?);
    items.extend(ctx.emit_float_runtime_items()?);
    items.extend(ctx.emit_ctors()?);
    items.extend(ctx.emit_recursors()?);
    items.extend(ctx.emit_closure_bodies(program)?);
    items.extend(ctx.emit_def_bodies(program)?);
    items.push(ctx.emit_main(program)?);

    Ok(render_items(&items))
}

struct CodegenContext<'a> {
    env: &'a Env,
    ids: &'a IdRegistry,
    adt_layouts: &'a AdtLayoutRegistry,
    adt_name_map: HashMap<AdtId, String>,
    ctor_name_map: HashMap<CtorId, String>,
    used_adts: Vec<AdtId>,
    boxed_fields: HashSet<(AdtId, usize, usize)>,
    recursor_sigs: HashMap<(AdtId, String), RecursorSignature>,
    recursor_specs: Vec<RecursorSpec>,
    recursor_lookup: HashMap<(AdtId, String), String>,
    closure_usage: HashMap<usize, ClosureUsage>,
    prop_adts: HashSet<AdtId>,
}

impl<'a> CodegenContext<'a> {
    fn new(env: &'a Env, ids: &'a IdRegistry) -> Result<Self, TypedCodegenError> {
        let adt_layouts = ids.adt_layouts();
        let mut adt_name_map = HashMap::new();
        let mut ctor_name_map = HashMap::new();
        let mut prop_adts = HashSet::new();

        for (name, decl) in &env.inductives {
            let adt_id = ids.adt_id(name).unwrap_or_else(|| AdtId::new(name));
            adt_name_map.insert(adt_id.clone(), sanitize_name(name));
            if inductive_result_sort_is_prop(decl.ty.as_ref()) {
                prop_adts.insert(adt_id.clone());
            }
            for (idx, ctor) in decl.ctors.iter().enumerate() {
                let ctor_id = CtorId::new(adt_id.clone(), idx);
                ctor_name_map.insert(ctor_id, sanitize_name(&ctor.name));
            }
        }

        Ok(Self {
            env,
            ids,
            adt_layouts,
            adt_name_map,
            ctor_name_map,
            used_adts: Vec::new(),
            boxed_fields: HashSet::new(),
            recursor_sigs: HashMap::new(),
            recursor_specs: Vec::new(),
            recursor_lookup: HashMap::new(),
            closure_usage: HashMap::new(),
            prop_adts,
        })
    }

    fn check_program_supported(&mut self, program: &TypedProgram) -> Result<(), TypedCodegenError> {
        let mut used_adts = HashSet::new();
        for body in program.defs.iter().chain(program.closures.iter()) {
            self.check_body_supported(body, &mut used_adts)?;
        }
        let mut used: Vec<_> = used_adts.into_iter().collect();
        used.sort_by(|a, b| self.adt_name(a).cmp(self.adt_name(b)));
        self.used_adts = used;
        self.compute_boxed_fields()?;
        self.finalize_recursors()?;
        self.collect_closure_usage(program)?;
        Ok(())
    }

    fn compute_boxed_fields(&mut self) -> Result<(), TypedCodegenError> {
        let mut boxed = HashSet::new();
        for adt_id in &self.used_adts {
            if adt_id.is_builtin(Builtin::Nat) || adt_id.is_builtin(Builtin::Bool) {
                continue;
            }
            let layout = self
                .adt_layouts
                .get(adt_id)
                .ok_or_else(|| TypedCodegenError::new("missing ADT layout"))?;
            for (variant_idx, variant) in layout.variants.iter().enumerate() {
                for (field_idx, field_ty) in variant.fields.iter().enumerate() {
                    if self.is_direct_recursive(field_ty, adt_id) {
                        boxed.insert((adt_id.clone(), variant_idx, field_idx));
                    }
                }
            }
        }
        self.boxed_fields = boxed;
        Ok(())
    }

    fn check_body_supported(
        &mut self,
        body: &TypedBody,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        for decl in &body.body.local_decls {
            self.check_type_supported(&decl.ty, used_adts)
                .map_err(|e| {
                    e.with_context(format!("typed backend unsupported in {}", body.name))
                })?;
            for cap_ty in &decl.closure_captures {
                self.check_type_supported(cap_ty, used_adts).map_err(|e| {
                    e.with_context(format!("typed backend unsupported in {}", body.name))
                })?;
            }
        }

        for block in &body.body.basic_blocks {
            for stmt in &block.statements {
                self.check_statement_supported(body, stmt, used_adts)?;
            }
            if let Some(term) = &block.terminator {
                self.check_terminator_supported(body, term, used_adts)?;
            }
        }
        Ok(())
    }

    fn check_type_supported(
        &self,
        ty: &MirType,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match ty {
            MirType::Unit | MirType::Bool | MirType::Nat => Ok(()),
            MirType::IndexTerm(_) => Ok(()),
            MirType::Adt(adt, args) => {
                if self.prop_adts.contains(adt) {
                    return Ok(());
                }
                used_adts.insert(adt.clone());
                for arg in args {
                    self.check_type_supported(arg, used_adts)?;
                }
                Ok(())
            }
            MirType::Fn(kind, _regions, args, ret)
            | MirType::FnItem(_, kind, _regions, args, ret)
            | MirType::Closure(kind, _, _regions, args, ret) => {
                let _ = kind;
                if args.len() != 1 {
                    return Err(TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedNonUnaryFunction,
                        "only unary (curried) function args are supported",
                    ));
                }
                for arg in args {
                    self.check_type_supported(arg, used_adts)?;
                }
                self.check_type_supported(ret, used_adts)
            }
            MirType::Ref(_, inner, _) => self.check_type_supported(inner, used_adts),
            MirType::RawPtr(inner, _) => self.check_type_supported(inner, used_adts),
            MirType::InteriorMutable(inner, _) => self.check_type_supported(inner, used_adts),
            MirType::Opaque { .. } => Ok(()),
            MirType::Param(_) => Ok(()),
        }
    }

    fn check_statement_supported(
        &mut self,
        body: &TypedBody,
        stmt: &Statement,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match stmt {
            Statement::Assign(place, rvalue) => {
                self.check_place_supported(body, place, used_adts)?;
                self.check_rvalue_supported(body, rvalue, used_adts)?;
                if let Rvalue::Use(Operand::Constant(constant)) = rvalue {
                    if let Literal::Recursor(ind_name) = &constant.literal {
                        self.record_recursor_signature(body, place, ind_name, used_adts)?;
                    }
                }
                Ok(())
            }
            Statement::RuntimeCheck(check) => {
                self.check_runtime_check_supported(body, check, used_adts)
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => Ok(()),
        }
    }

    fn check_terminator_supported(
        &self,
        body: &TypedBody,
        term: &Terminator,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match term {
            Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => Ok(()),
            Terminator::SwitchInt { discr, .. } => {
                self.check_operand_supported(body, discr, used_adts)?;
                Ok(())
            }
            Terminator::Call {
                func,
                args,
                destination,
                ..
            } => {
                self.check_call_operand_supported(body, func, used_adts)?;
                for arg in args {
                    self.check_operand_supported(body, arg, used_adts)?;
                }
                self.check_place_supported(body, destination, used_adts)?;
                Ok(())
            }
        }
    }

    fn check_rvalue_supported(
        &self,
        body: &TypedBody,
        rvalue: &Rvalue,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match rvalue {
            Rvalue::Use(op) => self.check_operand_supported(body, op, used_adts),
            Rvalue::Discriminant(place) => self.check_place_supported(body, place, used_adts),
            Rvalue::Ref(_, place) => self.check_place_supported(body, place, used_adts),
        }
    }

    fn check_runtime_check_supported(
        &self,
        body: &TypedBody,
        check: &RuntimeCheckKind,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match check {
            RuntimeCheckKind::RefCellBorrow { local } | RuntimeCheckKind::MutexLock { local } => {
                let ty = self.local_type(body, local.index()).ok_or_else(|| {
                    TypedCodegenError::new(format!(
                        "unknown local in runtime check in {}",
                        body.name
                    ))
                })?;
                self.check_type_supported(ty, used_adts)
            }
            RuntimeCheckKind::BoundsCheck { local, index } => {
                let container_ty = self.local_type(body, local.index()).ok_or_else(|| {
                    TypedCodegenError::new(format!("unknown container local in {}", body.name))
                })?;
                let index_ty = self.local_type(body, index.index()).ok_or_else(|| {
                    TypedCodegenError::new(format!("unknown index local in {}", body.name))
                })?;
                self.check_type_supported(container_ty, used_adts)?;
                self.check_type_supported(index_ty, used_adts)
            }
        }
    }

    fn check_operand_supported(
        &self,
        body: &TypedBody,
        op: &Operand,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                self.check_place_supported(body, place, used_adts)
            }
            Operand::Constant(constant) => self.check_constant_supported(body, constant, used_adts),
        }
    }

    fn check_call_operand_supported(
        &self,
        body: &TypedBody,
        op: &CallOperand,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        match op {
            CallOperand::Operand(op) => self.check_operand_supported(body, op, used_adts),
            CallOperand::Borrow(_, place) => {
                self.check_place_supported(body, place, used_adts)?;
                let ty = self.place_type(body, place).ok_or_else(|| {
                    TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedCallOperand,
                        format!("unsupported call operand in {}", body.name),
                    )
                })?;
                if !self.is_fn_type(&ty) {
                    return Err(TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedCallOperand,
                        format!(
                            "borrowed call operand must be a function in {} (local _{} has type {:?})",
                            body.name,
                            place.local.index(),
                            ty
                        ),
                    ));
                }
                Ok(())
            }
        }
    }

    fn check_constant_supported(
        &self,
        body: &TypedBody,
        constant: &Constant,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        self.check_type_supported(&constant.ty, used_adts)?;
        match &constant.literal {
            Literal::Unit | Literal::Nat(_) | Literal::Bool(_) => Ok(()),
            Literal::GlobalDef(name) => {
                if self.ids.def_id(name).is_some() {
                    Ok(())
                } else {
                    Err(TypedCodegenError::new(format!(
                        "unknown constant '{}' in {}",
                        name, body.name
                    )))
                }
            }
            Literal::Recursor(ind_name) => {
                let _ = self.check_recursor_supported(ind_name)?;
                Ok(())
            }
            Literal::OpaqueConst(_) => Ok(()),
            Literal::InductiveCtor(ctor, _, _) => {
                used_adts.insert(ctor.adt.clone());
                Ok(())
            }
            Literal::Closure(_, _) | Literal::Fix(_, _) => Ok(()),
        }
    }

    fn check_place_supported(
        &self,
        body: &TypedBody,
        place: &Place,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        if self.is_closure_body(&body.body) && place.local.index() == 1 {
            if !place.projection.is_empty() {
                if let PlaceElem::Field(idx) = place.projection[0] {
                    let captures = self.closure_capture_types(&body.body)?;
                    let cap_ty = captures.get(idx).ok_or_else(|| {
                        TypedCodegenError::new(format!(
                            "invalid closure capture index in {}",
                            body.name
                        ))
                    })?;
                    self.check_type_supported(cap_ty, used_adts)?;

                    let mut current_ty = cap_ty.clone();
                    let mut variant = None;
                    for proj in place.projection.iter().skip(1) {
                        match proj {
                            PlaceElem::Downcast(idx) => {
                                variant = Some(*idx);
                            }
                            PlaceElem::Field(field_idx) => {
                                if matches!(current_ty, MirType::Nat) {
                                    if variant == Some(1) && *field_idx == 0 {
                                        current_ty = MirType::Nat;
                                        variant = None;
                                        continue;
                                    }
                                    return Err(TypedCodegenError::unsupported(
                                        TypedCodegenReason::UnsupportedPlaceProjection,
                                        format!("unsupported Nat field access in {}", body.name),
                                    ));
                                }

                                current_ty = if let Some(next_ty) =
                                    self.field_type(&current_ty, variant, *field_idx)
                                {
                                    next_ty
                                } else if let MirType::Adt(adt_id, args) = &current_ty {
                                    self.field_type_without_downcast(adt_id, *field_idx, args)
                                        .ok_or_else(|| {
                                            TypedCodegenError::unsupported(
                                                TypedCodegenReason::UnsupportedPlaceProjection,
                                                format!(
                                                    "unsupported field access in {}",
                                                    body.name
                                                ),
                                            )
                                        })?
                                } else {
                                    return Err(TypedCodegenError::unsupported(
                                        TypedCodegenReason::UnsupportedPlaceProjection,
                                        format!("unsupported field access in {}", body.name),
                                    ));
                                };
                                self.check_type_supported(&current_ty, used_adts)?;
                                variant = None;
                            }
                            PlaceElem::Deref => {
                                current_ty = match current_ty {
                                    MirType::Ref(_, inner, _) | MirType::RawPtr(inner, _) => *inner,
                                    _ => {
                                        return Err(TypedCodegenError::unsupported(
                                            TypedCodegenReason::UnsupportedPlaceProjection,
                                            format!(
                                                "deref projection on non-reference in {}",
                                                body.name
                                            ),
                                        ))
                                    }
                                };
                                self.check_type_supported(&current_ty, used_adts)?;
                                variant = None;
                            }
                            PlaceElem::Index(_) => {
                                current_ty = self
                                    .index_item_type_for_container(&current_ty)
                                    .ok_or_else(|| {
                                        TypedCodegenError::unsupported(
                                            TypedCodegenReason::UnsupportedPlaceProjection,
                                            format!(
                                                "index projection on unsupported container in {}",
                                                body.name
                                            ),
                                        )
                                    })?;
                                self.check_type_supported(&current_ty, used_adts)?;
                                variant = None;
                            }
                        }
                    }
                    return Ok(());
                }
            }
            return Err(TypedCodegenError::unsupported(
                TypedCodegenReason::UnsupportedClosureEnvProjection,
                format!("unsupported closure env projection in {}", body.name),
            ));
        }

        let mut current_ty = self
            .local_type(body, place.local.index())
            .ok_or_else(|| {
                TypedCodegenError::new(format!("unknown local in place in {}", body.name))
            })?
            .clone();
        self.check_type_supported(&current_ty, used_adts)?;

        let mut variant = None;
        for proj in &place.projection {
            match proj {
                PlaceElem::Downcast(idx) => {
                    variant = Some(*idx);
                }
                PlaceElem::Field(field_idx) => {
                    if matches!(current_ty, MirType::Nat) {
                        if variant == Some(1) && *field_idx == 0 {
                            current_ty = MirType::Nat;
                            variant = None;
                            continue;
                        }
                        return Err(TypedCodegenError::unsupported(
                            TypedCodegenReason::UnsupportedPlaceProjection,
                            format!("unsupported Nat field access in {}", body.name),
                        ));
                    }

                    current_ty =
                        if let Some(next_ty) = self.field_type(&current_ty, variant, *field_idx) {
                            next_ty
                        } else if let MirType::Adt(adt_id, args) = &current_ty {
                            self.field_type_without_downcast(adt_id, *field_idx, args)
                                .ok_or_else(|| {
                                    TypedCodegenError::unsupported(
                                        TypedCodegenReason::UnsupportedPlaceProjection,
                                        format!("unsupported field access in {}", body.name),
                                    )
                                })?
                        } else {
                            return Err(TypedCodegenError::unsupported(
                                TypedCodegenReason::UnsupportedPlaceProjection,
                                format!("unsupported field access in {}", body.name),
                            ));
                        };
                    self.check_type_supported(&current_ty, used_adts)?;
                    variant = None;
                }
                PlaceElem::Deref => {
                    current_ty = match current_ty {
                        MirType::Ref(_, inner, _) | MirType::RawPtr(inner, _) => *inner,
                        _ => {
                            return Err(TypedCodegenError::unsupported(
                                TypedCodegenReason::UnsupportedPlaceProjection,
                                format!("deref projection on non-reference in {}", body.name),
                            ))
                        }
                    };
                    self.check_type_supported(&current_ty, used_adts)?;
                    variant = None;
                }
                PlaceElem::Index(_) => {
                    current_ty =
                        self.index_item_type_for_container(&current_ty)
                            .ok_or_else(|| {
                                TypedCodegenError::unsupported(
                                    TypedCodegenReason::UnsupportedPlaceProjection,
                                    format!(
                                        "index projection on unsupported container in {}",
                                        body.name
                                    ),
                                )
                            })?;
                    self.check_type_supported(&current_ty, used_adts)?;
                    variant = None;
                }
            }
        }
        Ok(())
    }

    fn emit_adts(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let mut items = Vec::new();
        for adt_id in &self.used_adts {
            if adt_id.is_builtin(Builtin::Nat) || adt_id.is_builtin(Builtin::Bool) {
                continue;
            }
            if self.prop_adts.contains(adt_id) {
                continue;
            }
            let adt_name = self.adt_name(adt_id);
            let generics = self.adt_generic_params(adt_id);
            let adt_decl_name = self.name_with_generics(adt_name, &generics);
            let Some(layout) = self.adt_layouts.get(adt_id) else {
                return Err(TypedCodegenError::new("missing ADT layout"));
            };
            let mut variants = Vec::new();
            for (variant_idx, variant) in layout.variants.iter().enumerate() {
                let ctor_name = self
                    .ctor_name_map
                    .get(&variant.ctor)
                    .cloned()
                    .unwrap_or_else(|| format!("Ctor{}", variant_idx));
                let mut fields = Vec::new();
                for (field_idx, field_ty) in variant.fields.iter().enumerate() {
                    let ty = self.rust_field_type(adt_id, variant_idx, field_idx, field_ty)?;
                    fields.push(ty);
                }
                variants.push(EnumVariant {
                    name: ctor_name,
                    fields,
                });
            }
            if !generics.is_empty() {
                variants.push(EnumVariant {
                    name: "__Phantom".to_string(),
                    fields: vec![format!(
                        "std::marker::PhantomData<({})>",
                        generics.join(", ")
                    )],
                });
            }
            items.push(Item::Enum {
                name: adt_decl_name,
                derives: vec!["Clone".to_string()],
                variants,
            });
        }
        Ok(items)
    }

    fn emit_callable_runtime_items(&self) -> Vec<Item> {
        vec![Item::Raw(
            r#"
trait LrlCallable<Arg, Ret>: 'static {
    fn call(&self, arg: Arg) -> Ret;
}

impl<Arg, Ret, F> LrlCallable<Arg, Ret> for F
where
    F: Fn(Arg) -> Ret + 'static,
{
    fn call(&self, arg: Arg) -> Ret {
        self(arg)
    }
}

#[derive(Clone)]
struct LrlClosureAdapter<Cap, Arg, Ret> {
    cap: Cap,
    func: fn(Cap, Arg) -> Ret,
}

impl<Cap, Arg, Ret> LrlCallable<Arg, Ret> for LrlClosureAdapter<Cap, Arg, Ret>
where
    Cap: Clone + 'static,
    Arg: 'static,
    Ret: 'static,
{
    fn call(&self, arg: Arg) -> Ret {
        (self.func)(self.cap.clone(), arg)
    }
}

#[derive(Clone)]
struct LrlFixAdapter<Cap, Arg, Ret> {
    self_ref: std::rc::Weak<LrlFixAdapter<Cap, Arg, Ret>>,
    cap: Cap,
    func: fn(Rc<dyn LrlCallable<Arg, Ret>>, Cap, Arg) -> Ret,
}

impl<Cap, Arg, Ret> LrlCallable<Arg, Ret> for LrlFixAdapter<Cap, Arg, Ret>
where
    Cap: Clone + 'static,
    Arg: 'static,
    Ret: 'static,
{
    fn call(&self, arg: Arg) -> Ret {
        let self_rc = self.self_ref.upgrade().expect("self ref");
        let self_dyn: Rc<dyn LrlCallable<Arg, Ret>> = self_rc;
        (self.func)(self_dyn, self.cap.clone(), arg)
    }
}

#[derive(Clone, Debug)]
struct LrlRefShared<T> {
    value: T,
}

impl<T> LrlRefShared<T> {
    fn from_value(value: T) -> Self {
        Self { value }
    }
}

impl<T: Clone> LrlRefShared<T> {
    fn read(&self) -> T {
        self.value.clone()
    }
}

#[derive(Clone, Debug)]
struct LrlRefMut<T> {
    value: T,
}

impl<T> LrlRefMut<T> {
    fn from_value(value: T) -> Self {
        Self { value }
    }
}

impl<T: Clone> LrlRefMut<T> {
    fn read(&self) -> T {
        self.value.clone()
    }
}

#[derive(Clone, Debug)]
struct LrlRefCell<T> {
    value: T,
}

#[derive(Clone, Debug)]
struct LrlMutex<T> {
    value: T,
}

#[derive(Clone, Debug)]
struct LrlAtomic<T> {
    value: T,
}

#[derive(Clone, Debug)]
struct LrlOpaque {
    reason: String,
}

impl LrlOpaque {
    fn new(reason: &str) -> Self {
        Self {
            reason: reason.to_string(),
        }
    }
}

fn runtime_refcell_borrow_check<T>(_value: T) {}

fn runtime_mutex_lock<T>(_value: T) {}

fn runtime_bounds_check<TContainer, TIndex>(_container: TContainer, _index: TIndex) {}

trait LrlIndex<TItem> {
    fn lrl_index(self, index: usize) -> TItem;
}

fn runtime_index<TItem, TContainer>(container: TContainer, index: u64) -> TItem
where
    TContainer: LrlIndex<TItem>,
{
    container.lrl_index(index as usize)
}

fn runtime_raw_ptr_read<T: Clone>(ptr: *const T) -> T {
    // Pointer validity is guaranteed by MIR borrow/raw-pointer analyses before codegen.
    unsafe { (*ptr).clone() }
}

fn runtime_raw_ptr_read_mut<T: Clone>(ptr: *mut T) -> T {
    // Pointer validity is guaranteed by MIR borrow/raw-pointer analyses before codegen.
    unsafe { (*ptr).clone() }
}
"#
            .trim()
            .to_string(),
        )]
    }

    fn emit_index_runtime_impls(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let mut items = Vec::new();
        let list_builtin = self.ids.builtin_adt(Builtin::List);
        for adt_id in &self.used_adts {
            let is_indexable = self.ids.is_indexable_adt(adt_id);
            let is_builtin_list = list_builtin.as_ref().is_some_and(|id| id == adt_id);
            if !is_indexable && !is_builtin_list {
                continue;
            }

            let adt_name = self.adt_name(adt_id).to_string();
            let generics = self.adt_generic_params(adt_id);
            let layout = self
                .adt_layouts
                .get(adt_id)
                .ok_or_else(|| TypedCodegenError::new("missing ADT layout"))?;

            if is_builtin_list {
                if layout.variants.len() != 2 {
                    continue;
                }
                let nil_ctor = self
                    .ctor_name_map
                    .get(&layout.variants[0].ctor)
                    .cloned()
                    .unwrap_or_else(|| "nil".to_string());
                let cons_ctor = self
                    .ctor_name_map
                    .get(&layout.variants[1].ctor)
                    .cloned()
                    .unwrap_or_else(|| "cons".to_string());
                if layout.variants[1].fields.len() < 2 || generics.is_empty() {
                    continue;
                }
                let impl_generics = format!("<{}>", generics.join(", "));
                let adt_ty = self.name_with_generics(&adt_name, &generics);
                let item_ty = generics[0].clone();
                let text = format!(
                    "impl{} LrlIndex<{}> for {} {{
    fn lrl_index(self, index: usize) -> {} {{
        let mut current = self;
        let mut i = index;
        loop {{
            match current {{
                {}::{} => panic!(\"index out of bounds\"),
                {}::{}(head, tail) => {{
                    if i == 0 {{
                        return head;
                    }}
                    i -= 1;
                    current = *tail;
                }},
                _ => panic!(\"indexing shape unsupported in typed backend\"),
            }}
        }}
    }}
}}",
                    impl_generics,
                    item_ty,
                    adt_ty,
                    item_ty,
                    adt_name,
                    nil_ctor,
                    adt_name,
                    cons_ctor
                );
                items.push(Item::Raw(text));
                continue;
            }

            if !is_indexable {
                continue;
            }

            let item_ty_mir = if !generics.is_empty() {
                MirType::Param(0)
            } else if let Some(inferred) = self.infer_monomorphic_index_item_type(adt_id) {
                inferred
            } else {
                continue;
            };
            let impl_generics = if generics.is_empty() {
                String::new()
            } else {
                format!("<{}>", generics.join(", "))
            };
            let adt_ty = self.name_with_generics(&adt_name, &generics);
            let item_ty = self.rust_type(&item_ty_mir)?;

            let mut arms = Vec::new();
            for (variant_idx, variant) in layout.variants.iter().enumerate() {
                let ctor_name = self
                    .ctor_name_map
                    .get(&variant.ctor)
                    .cloned()
                    .unwrap_or_else(|| format!("Ctor{}", variant_idx));

                let source = self.select_index_source_field(&variant.fields, &item_ty_mir);
                let bind_idx = source.as_ref().map(|(idx, _)| *idx);
                let bind_name = bind_idx.map(|idx| format!("field_{}", idx));
                let pattern = if variant.fields.is_empty() {
                    format!("{}::{}", adt_name, ctor_name)
                } else {
                    let parts: Vec<String> = (0..variant.fields.len())
                        .map(|idx| match (&bind_idx, &bind_name) {
                            (Some(target), Some(name)) if idx == *target => name.clone(),
                            _ => "_".to_string(),
                        })
                        .collect();
                    format!("{}::{}({})", adt_name, ctor_name, parts.join(", "))
                };

                let body_expr = match (source, bind_name) {
                    (Some((field_idx, IndexSourceKind::Direct)), Some(name)) => {
                        let value_expr =
                            if self
                                .boxed_fields
                                .contains(&(adt_id.clone(), variant_idx, field_idx))
                            {
                                format!("*{}", name)
                            } else {
                                name
                            };
                        format!(
                            "if index == 0 {{ {} }} else {{ panic!(\"index out of bounds\") }}",
                            value_expr
                        )
                    }
                    (Some((field_idx, IndexSourceKind::Nested)), Some(name)) => {
                        let source_expr =
                            if self
                                .boxed_fields
                                .contains(&(adt_id.clone(), variant_idx, field_idx))
                            {
                                format!("*{}", name)
                            } else {
                                name
                            };
                        format!("runtime_index({}, index as u64)", source_expr)
                    }
                    _ => "panic!(\"index out of bounds\")".to_string(),
                };
                arms.push(format!("{} => {}", pattern, body_expr));
            }
            if arms.is_empty() {
                continue;
            }

            let text = format!(
                "impl{} LrlIndex<{}> for {} {{
    fn lrl_index(self, index: usize) -> {} {{
        match self {{
            {},
            _ => panic!(\"index out of bounds\"),
        }}
    }}
}}",
                impl_generics,
                item_ty,
                adt_ty,
                item_ty,
                arms.join(",\n            ")
            );
            items.push(Item::Raw(text));
        }
        Ok(items)
    }

    fn emit_text_io_runtime_items(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let Some(text_adt_id) = self.ids.adt_id("Text") else {
            return Ok(Vec::new());
        };
        let Some(list_adt_id) = self.ids.adt_id("List") else {
            return Ok(Vec::new());
        };

        let text_ty = self.rust_type(&MirType::Adt(text_adt_id.clone(), Vec::new()))?;
        let list_nat_ty = self.rust_type(&MirType::Adt(list_adt_id.clone(), vec![MirType::Nat]))?;

        let text_enum = self.adt_name(&text_adt_id).to_string();
        let list_enum = self.adt_name(&list_adt_id).to_string();
        let text_ctor = self
            .ctor_name_map
            .get(&CtorId::new(text_adt_id, 0))
            .cloned()
            .unwrap_or_else(|| "text".to_string());
        let list_nil_ctor = self
            .ctor_name_map
            .get(&CtorId::new(list_adt_id.clone(), 0))
            .cloned()
            .unwrap_or_else(|| "nil".to_string());
        let list_cons_ctor = self
            .ctor_name_map
            .get(&CtorId::new(list_adt_id, 1))
            .cloned()
            .unwrap_or_else(|| "cons".to_string());

        let runtime_helpers = format!(
            "fn runtime_list_nat_to_string(mut list: {list_nat_ty}) -> String {{
    let mut output = String::new();
    loop {{
        match list {{
            {list_enum}::{list_nil_ctor} => return output,
            {list_enum}::{list_cons_ctor}(head, tail) => {{
                if let Some(ch) = char::from_u32(head as u32) {{
                    output.push(ch);
                }}
                list = *tail;
            }},
            _ => return output,
        }}
    }}
}}

fn runtime_string_to_list_nat(input: &str) -> {list_nat_ty} {{
    input
        .chars()
        .rev()
        .fold({list_enum}::{list_nil_ctor}, |acc, ch| {list_enum}::{list_cons_ctor}(ch as u64, Box::new(acc)))
}}

fn runtime_string_to_text(input: &str) -> {text_ty} {{
    {text_enum}::{text_ctor}(runtime_string_to_list_nat(input))
}}

fn runtime_text_to_string(value: {text_ty}) -> String {{
    match value {{
        {text_enum}::{text_ctor}(data) => runtime_list_nat_to_string(data),
        _ => String::new(),
    }}
}}

fn runtime_read_file_text(path: {text_ty}) -> {text_ty} {{
    let path_string = runtime_text_to_string(path);
    match std::fs::read_to_string(&path_string) {{
        Ok(content) => runtime_string_to_text(&content),
        Err(_) => runtime_string_to_text(\"\"), 
    }}
}}

fn runtime_write_file_text(path: {text_ty}, contents: {text_ty}) -> {text_ty} {{
    let path_string = runtime_text_to_string(path);
    let content_string = runtime_text_to_string(contents.clone());
    let _ = std::fs::write(&path_string, &content_string);
    contents
}}",
        );

        Ok(vec![Item::Raw(runtime_helpers)])
    }

    fn emit_int_runtime_items(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let Some(int_adt_id) = self.ids.adt_id("Int") else {
            return Ok(Vec::new());
        };
        if !self.used_adts.contains(&int_adt_id) {
            return Ok(Vec::new());
        }

        let int_ty = self.rust_type(&MirType::Adt(int_adt_id.clone(), Vec::new()))?;
        let int_enum = self.adt_name(&int_adt_id).to_string();
        let int_pos_ctor = self
            .ctor_name_map
            .get(&CtorId::new(int_adt_id.clone(), 0))
            .cloned()
            .unwrap_or_else(|| "int_pos".to_string());
        let int_neg_ctor = self
            .ctor_name_map
            .get(&CtorId::new(int_adt_id, 1))
            .cloned()
            .unwrap_or_else(|| "int_neg".to_string());

        let runtime_helper = format!(
            "fn runtime_int_to_string(value: {int_ty}) -> String {{
    match value {{
        {int_enum}::{int_pos_ctor}(magnitude) => magnitude.to_string(),
        {int_enum}::{int_neg_ctor}(magnitude) => {{
            if magnitude == 0 {{
                \"0\".to_string()
            }} else {{
                format!(\"-{{}}\", magnitude)
            }}
        }},
        _ => String::new(),
    }}
}}",
        );

        Ok(vec![Item::Raw(runtime_helper)])
    }

    fn emit_float_runtime_items(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let Some(float_adt_id) = self.ids.adt_id("Float") else {
            return Ok(Vec::new());
        };

        let float_ty = self.rust_type(&MirType::Adt(float_adt_id.clone(), Vec::new()))?;
        let float_enum = self.adt_name(&float_adt_id).to_string();
        let float_ctor = self
            .ctor_name_map
            .get(&CtorId::new(float_adt_id, 0))
            .cloned()
            .unwrap_or_else(|| "float16".to_string());

        let runtime_helpers = format!(
            "fn runtime_f16_bits_to_f32(bits: u16) -> f32 {{
    let sign = ((bits & 0x8000) as u32) << 16;
    let exp = ((bits >> 10) & 0x1f) as u32;
    let mant = (bits & 0x03ff) as u32;

    let f_bits = if exp == 0 {{
        if mant == 0 {{
            sign
        }} else {{
            let mut mantissa = mant;
            let mut exponent: i32 = -14;
            while (mantissa & 0x0400) == 0 {{
                mantissa <<= 1;
                exponent -= 1;
            }}
            mantissa &= 0x03ff;
            let exp32 = ((exponent + 127) as u32) << 23;
            sign | exp32 | (mantissa << 13)
        }}
    }} else if exp == 0x1f {{
        sign | 0x7f80_0000 | (mant << 13)
    }} else {{
        let exp32 = ((exp as i32 - 15 + 127) as u32) << 23;
        sign | exp32 | (mant << 13)
    }};

    f32::from_bits(f_bits)
}}

fn runtime_f32_to_f16_bits(value: f32) -> u16 {{
    let bits = value.to_bits();
    let sign = ((bits >> 16) & 0x8000) as u16;
    let exp = ((bits >> 23) & 0xff) as i32;
    let mantissa = bits & 0x007f_ffff;

    if exp == 0xff {{
        if mantissa == 0 {{
            return sign | 0x7c00;
        }}
        return sign | 0x7e00;
    }}

    let exp16 = exp - 127 + 15;
    if exp16 >= 0x1f {{
        return sign | 0x7c00;
    }}

    if exp16 <= 0 {{
        if exp16 < -10 {{
            return sign;
        }}
        let mantissa_with_hidden = mantissa | 0x0080_0000;
        let shift = (14 - exp16) as u32;
        let mut half_mantissa = (mantissa_with_hidden >> shift) as u16;
        let round_bit = (mantissa_with_hidden >> (shift - 1)) & 1;
        if round_bit == 1 {{
            half_mantissa = half_mantissa.saturating_add(1);
        }}
        return sign | half_mantissa;
    }}

    let mut half_exp = (exp16 as u16) << 10;
    let mut half_mantissa = (mantissa >> 13) as u16;
    if (mantissa & 0x0000_1000) != 0 {{
        half_mantissa = half_mantissa.saturating_add(1);
        if (half_mantissa & 0x0400) != 0 {{
            half_mantissa = 0;
            half_exp = half_exp.saturating_add(0x0400);
            if half_exp >= 0x7c00 {{
                return sign | 0x7c00;
            }}
        }}
    }}
    sign | half_exp | (half_mantissa & 0x03ff)
}}

fn runtime_float_to_f32(value: {float_ty}) -> f32 {{
    match value {{
        {float_enum}::{float_ctor}(bits) => runtime_f16_bits_to_f32(bits as u16),
        _ => 0.0,
    }}
}}

fn runtime_f32_to_float(value: f32) -> {float_ty} {{
    {float_enum}::{float_ctor}(runtime_f32_to_f16_bits(value) as u64)
}}

fn runtime_float_add(lhs: {float_ty}, rhs: {float_ty}) -> {float_ty} {{
    runtime_f32_to_float(runtime_float_to_f32(lhs) + runtime_float_to_f32(rhs))
}}

fn runtime_float_sub(lhs: {float_ty}, rhs: {float_ty}) -> {float_ty} {{
    runtime_f32_to_float(runtime_float_to_f32(lhs) - runtime_float_to_f32(rhs))
}}

fn runtime_float_mul(lhs: {float_ty}, rhs: {float_ty}) -> {float_ty} {{
    runtime_f32_to_float(runtime_float_to_f32(lhs) * runtime_float_to_f32(rhs))
}}

fn runtime_float_div(lhs: {float_ty}, rhs: {float_ty}) -> {float_ty} {{
    runtime_f32_to_float(runtime_float_to_f32(lhs) / runtime_float_to_f32(rhs))
}}

fn runtime_float_to_string(value: {float_ty}) -> String {{
    runtime_float_to_f32(value).to_string()
}}",
        );

        Ok(vec![Item::Raw(runtime_helpers)])
    }

    fn collect_closure_usage(&mut self, program: &TypedProgram) -> Result<(), TypedCodegenError> {
        let mut usage: HashMap<usize, ClosureUsage> = HashMap::new();
        for body in program.defs.iter().chain(program.closures.iter()) {
            self.collect_closure_usage_in_body(body, &mut usage)?;
        }
        self.closure_usage = usage;
        Ok(())
    }

    fn collect_closure_usage_in_body(
        &self,
        body: &TypedBody,
        usage: &mut HashMap<usize, ClosureUsage>,
    ) -> Result<(), TypedCodegenError> {
        for block in &body.body.basic_blocks {
            for stmt in &block.statements {
                if let Statement::Assign(_, rv) = stmt {
                    self.collect_closure_usage_in_rvalue(body, rv, usage)?;
                }
            }
            if let Some(term) = &block.terminator {
                self.collect_closure_usage_in_terminator(body, term, usage)?;
            }
        }
        Ok(())
    }

    fn collect_closure_usage_in_rvalue(
        &self,
        body: &TypedBody,
        rv: &Rvalue,
        usage: &mut HashMap<usize, ClosureUsage>,
    ) -> Result<(), TypedCodegenError> {
        match rv {
            Rvalue::Use(op) => self.collect_closure_usage_in_operand(body, op, usage),
            Rvalue::Discriminant(_) | Rvalue::Ref(_, _) => Ok(()),
        }
    }

    fn collect_closure_usage_in_terminator(
        &self,
        body: &TypedBody,
        term: &Terminator,
        usage: &mut HashMap<usize, ClosureUsage>,
    ) -> Result<(), TypedCodegenError> {
        match term {
            Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => Ok(()),
            Terminator::SwitchInt { discr, .. } => {
                self.collect_closure_usage_in_operand(body, discr, usage)
            }
            Terminator::Call { func, args, .. } => {
                self.collect_closure_usage_in_call_operand(body, func, usage)?;
                for arg in args {
                    self.collect_closure_usage_in_operand(body, arg, usage)?;
                }
                Ok(())
            }
        }
    }

    fn collect_closure_usage_in_call_operand(
        &self,
        body: &TypedBody,
        op: &CallOperand,
        usage: &mut HashMap<usize, ClosureUsage>,
    ) -> Result<(), TypedCodegenError> {
        match op {
            CallOperand::Operand(op) => self.collect_closure_usage_in_operand(body, op, usage),
            CallOperand::Borrow(_, _) => Ok(()),
        }
    }

    fn collect_closure_usage_in_operand(
        &self,
        body: &TypedBody,
        op: &Operand,
        usage: &mut HashMap<usize, ClosureUsage>,
    ) -> Result<(), TypedCodegenError> {
        let Operand::Constant(c) = op else {
            return Ok(());
        };

        match &c.literal {
            Literal::Closure(idx, captures) => {
                let global_idx = body.closure_base + *idx;
                let entry = usage.entry(global_idx).or_default();
                match entry.closure_capture_len {
                    Some(prev) if prev != captures.len() => Err(TypedCodegenError::new(format!(
                        "inconsistent closure capture shape for closure_{}",
                        global_idx
                    ))),
                    _ => {
                        entry.closure_capture_len = Some(captures.len());
                        Ok(())
                    }
                }
            }
            Literal::Fix(idx, captures) => {
                let global_idx = body.closure_base + *idx;
                let entry = usage.entry(global_idx).or_default();
                match entry.fix_capture_len {
                    Some(prev) if prev != captures.len() => Err(TypedCodegenError::new(format!(
                        "inconsistent fix capture shape for closure_{}",
                        global_idx
                    ))),
                    _ => {
                        entry.fix_capture_len = Some(captures.len());
                        Ok(())
                    }
                }
            }
            _ => Ok(()),
        }
    }

    fn emit_ctors(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let mut items = Vec::new();
        let mut names: Vec<_> = self.env.inductives.keys().cloned().collect();
        names.sort();

        for name in names {
            let Some(decl) = self.env.inductives.get(&name) else {
                continue;
            };
            let adt_id = self.ids.adt_id(&name).unwrap_or_else(|| AdtId::new(&name));
            if !self.used_adts.contains(&adt_id)
                && !adt_id.is_builtin(Builtin::Nat)
                && !adt_id.is_builtin(Builtin::Bool)
            {
                continue;
            }

            for (idx, ctor) in decl.ctors.iter().enumerate() {
                let ctor_id = CtorId::new(adt_id.clone(), idx);
                let ctor_name = self
                    .ctor_name_map
                    .get(&ctor_id)
                    .cloned()
                    .unwrap_or_else(|| sanitize_name(&ctor.name));
                let arity = self
                    .ids
                    .ctor_arity(&ctor_id)
                    .unwrap_or_else(|| count_arity(&ctor.ty));

                let generics = if self.prop_adts.contains(&adt_id) {
                    Vec::new()
                } else {
                    self.adt_generic_params(&adt_id)
                };

                let ctor_value_type = self.ctor_value_type(&adt_id, idx, arity)?;
                let ctor_expr = self.ctor_value_expr(&adt_id, idx, arity)?;
                items.push(Item::Fn {
                    name: self.fn_name_with_generics(&ctor_name, &generics),
                    params: Vec::new(),
                    ret: Some(ctor_value_type),
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(ctor_expr)),
                    },
                });
            }
        }
        Ok(items)
    }

    fn emit_recursors(&self) -> Result<Vec<Item>, TypedCodegenError> {
        let mut items = Vec::new();
        if self.recursor_specs.is_empty() {
            return Ok(items);
        }
        for spec in &self.recursor_specs {
            let mut rec_items = if spec.adt_id.is_builtin(Builtin::Nat) {
                self.emit_nat_recursor(spec)?
            } else if spec.adt_id.is_builtin(Builtin::Bool) {
                self.emit_bool_recursor(spec)?
            } else {
                self.emit_adt_recursor(spec)?
            };
            items.append(&mut rec_items);
        }
        Ok(items)
    }

    fn emit_closure_bodies(&self, program: &TypedProgram) -> Result<Vec<Item>, TypedCodegenError> {
        let mut items = Vec::new();
        for body in &program.closures {
            let global_idx = self.closure_body_index(body);
            items.push(self.emit_body(body, true)?);
            if self
                .closure_usage
                .get(&global_idx)
                .and_then(|u| u.closure_capture_len)
                .is_some()
            {
                items.push(self.emit_closure_adapter_fn(body, global_idx)?);
            }
            if self
                .closure_usage
                .get(&global_idx)
                .and_then(|u| u.fix_capture_len)
                .is_some()
            {
                items.push(self.emit_fix_adapter_fn(body, global_idx)?);
            }
        }
        Ok(items)
    }

    fn emit_def_bodies(&self, program: &TypedProgram) -> Result<Vec<Item>, TypedCodegenError> {
        let mut items = Vec::new();
        for body in &program.defs {
            if let Some(item) = self.emit_special_builtin(body)? {
                items.push(item);
                continue;
            }
            items.push(self.emit_body(body, false)?);
        }
        Ok(items)
    }

    fn emit_special_builtin(&self, body: &TypedBody) -> Result<Option<Item>, TypedCodegenError> {
        match body.name.as_str() {
            "print_nat" => self.emit_debug_print_builtin(body, "print_nat", &MirType::Nat),
            "print_bool" => self.emit_debug_print_builtin(body, "print_bool", &MirType::Bool),
            "print_float" => self.emit_float_print_builtin(body),
            "print_text" | "print" => {
                let text_ty = self.text_mir_type().ok_or_else(|| {
                    TypedCodegenError::new("Text type is required to emit text print builtins")
                })?;
                if !self.unary_identity_builtin_signature_matches(body, &text_ty) {
                    return Err(TypedCodegenError::new(format!(
                        "print builtin '{}' must have type {} -> {}",
                        body.name,
                        self.rust_type(&text_ty)?,
                        self.rust_type(&text_ty)?
                    )));
                }
                let arg_ty = self.rust_type(&text_ty)?;
                let ret_ty = self.curried_fn_type(&[arg_ty.clone()], arg_ty.clone());
                let arg_name = "value".to_string();
                let rendered = self.expr_call_path(
                    "runtime_text_to_string",
                    vec![self.expr_clone(self.expr_path(arg_name.clone()))],
                );
                let print_stmt = Stmt::Expr(Expr::MacroCall {
                    name: "println".to_string(),
                    args: vec![self.expr_lit_str("{}"), rendered],
                });
                let closure = Expr::Closure {
                    params: vec![Param {
                        name: arg_name.clone(),
                        ty: Some(arg_ty),
                    }],
                    body: Block {
                        stmts: vec![print_stmt],
                        tail: Some(Box::new(self.expr_path(arg_name))),
                    },
                    is_move: true,
                };
                let callable_expr = self.callable_literal_expr(&text_ty, &text_ty, closure)?;
                Ok(Some(Item::Fn {
                    name: body.name.clone(),
                    params: Vec::new(),
                    ret: Some(ret_ty),
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(callable_expr)),
                    },
                }))
            }
            "read_file" => {
                let text_ty = self.text_mir_type().ok_or_else(|| {
                    TypedCodegenError::new("Text type is required to emit read_file builtin")
                })?;
                if !self.unary_identity_builtin_signature_matches(body, &text_ty) {
                    return Err(TypedCodegenError::new(format!(
                        "read_file builtin must have type {} -> {}",
                        self.rust_type(&text_ty)?,
                        self.rust_type(&text_ty)?
                    )));
                }
                let arg_ty = self.rust_type(&text_ty)?;
                let ret_ty = self.curried_fn_type(&[arg_ty.clone()], arg_ty.clone());
                let arg_name = "path".to_string();
                let closure = Expr::Closure {
                    params: vec![Param {
                        name: arg_name.clone(),
                        ty: Some(arg_ty),
                    }],
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(self.expr_call_path(
                            "runtime_read_file_text",
                            vec![self.expr_path(arg_name)],
                        ))),
                    },
                    is_move: true,
                };
                let callable_expr = self.callable_literal_expr(&text_ty, &text_ty, closure)?;
                Ok(Some(Item::Fn {
                    name: body.name.clone(),
                    params: Vec::new(),
                    ret: Some(ret_ty),
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(callable_expr)),
                    },
                }))
            }
            "write_file" => {
                let text_ty = self.text_mir_type().ok_or_else(|| {
                    TypedCodegenError::new("Text type is required to emit write_file builtin")
                })?;
                if !self.write_file_builtin_signature_matches(body, &text_ty) {
                    return Err(TypedCodegenError::new(format!(
                        "write_file builtin must have type {} -> {} -> {}",
                        self.rust_type(&text_ty)?,
                        self.rust_type(&text_ty)?,
                        self.rust_type(&text_ty)?
                    )));
                }
                let text_rust_ty = self.rust_type(&text_ty)?;
                let ret_ty = self.curried_fn_type(
                    &[text_rust_ty.clone(), text_rust_ty.clone()],
                    text_rust_ty.clone(),
                );
                let outer_arg = "path".to_string();
                let inner_arg = "contents".to_string();
                let inner_closure = Expr::Closure {
                    params: vec![Param {
                        name: inner_arg.clone(),
                        ty: Some(text_rust_ty.clone()),
                    }],
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(self.expr_call_path(
                            "runtime_write_file_text",
                            vec![
                                self.expr_clone(self.expr_path(outer_arg.clone())),
                                self.expr_path(inner_arg),
                            ],
                        ))),
                    },
                    is_move: true,
                };
                let inner_callable_expr =
                    self.callable_literal_expr(&text_ty, &text_ty, inner_closure)?;
                let outer_ret_ty = match self.local_type(body, 0) {
                    Some(MirType::Fn(_, _, _, outer_ret))
                    | Some(MirType::FnItem(_, _, _, _, outer_ret))
                    | Some(MirType::Closure(_, _, _, _, outer_ret)) => outer_ret.as_ref(),
                    _ => {
                        return Err(TypedCodegenError::new(
                            "write_file builtin has invalid top-level function type",
                        ))
                    }
                };
                let outer_closure = Expr::Closure {
                    params: vec![Param {
                        name: outer_arg,
                        ty: Some(text_rust_ty),
                    }],
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(inner_callable_expr)),
                    },
                    is_move: true,
                };
                let outer_callable_expr =
                    self.callable_literal_expr(&text_ty, outer_ret_ty, outer_closure)?;
                Ok(Some(Item::Fn {
                    name: body.name.clone(),
                    params: Vec::new(),
                    ret: Some(ret_ty),
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(outer_callable_expr)),
                    },
                }))
            }
            "+f" | "_u2B_f" => self.emit_float_binary_builtin(body, "runtime_float_add"),
            "-f" | "_u2D_f" => self.emit_float_binary_builtin(body, "runtime_float_sub"),
            "*f" | "_u2A_f" => self.emit_float_binary_builtin(body, "runtime_float_mul"),
            "/f" | "_u2F_f" => self.emit_float_binary_builtin(body, "runtime_float_div"),
            _ => Ok(None),
        }
    }

    fn emit_float_print_builtin(
        &self,
        body: &TypedBody,
    ) -> Result<Option<Item>, TypedCodegenError> {
        let float_ty = self.float_mir_type().ok_or_else(|| {
            TypedCodegenError::new("Float type is required to emit print_float builtin")
        })?;
        if !self.unary_identity_builtin_signature_matches(body, &float_ty) {
            return Err(TypedCodegenError::new(format!(
                "print_float builtin must have type {} -> {}",
                self.rust_type(&float_ty)?,
                self.rust_type(&float_ty)?
            )));
        }

        let arg_ty = self.rust_type(&float_ty)?;
        let ret_ty = self.curried_fn_type(&[arg_ty.clone()], arg_ty.clone());
        let arg_name = "value".to_string();
        let rendered = self.expr_call_path(
            "runtime_float_to_f32",
            vec![self.expr_clone(self.expr_path(arg_name.clone()))],
        );
        let print_stmt = Stmt::Expr(Expr::MacroCall {
            name: "println".to_string(),
            args: vec![self.expr_lit_str("{}"), rendered],
        });
        let closure = Expr::Closure {
            params: vec![Param {
                name: arg_name.clone(),
                ty: Some(arg_ty),
            }],
            body: Block {
                stmts: vec![print_stmt],
                tail: Some(Box::new(self.expr_path(arg_name))),
            },
            is_move: true,
        };
        let callable_expr = self.callable_literal_expr(&float_ty, &float_ty, closure)?;
        Ok(Some(Item::Fn {
            name: body.name.clone(),
            params: Vec::new(),
            ret: Some(ret_ty),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(callable_expr)),
            },
        }))
    }

    fn emit_float_binary_builtin(
        &self,
        body: &TypedBody,
        runtime_fn: &str,
    ) -> Result<Option<Item>, TypedCodegenError> {
        let float_ty = self.float_mir_type().ok_or_else(|| {
            TypedCodegenError::new("Float type is required to emit float arithmetic builtins")
        })?;
        if !self.binary_curried_identity_builtin_signature_matches(body, &float_ty) {
            return Err(TypedCodegenError::new(format!(
                "float builtin '{}' must have type {} -> {} -> {}",
                body.name,
                self.rust_type(&float_ty)?,
                self.rust_type(&float_ty)?,
                self.rust_type(&float_ty)?
            )));
        }

        let float_rust_ty = self.rust_type(&float_ty)?;
        let ret_ty = self.curried_fn_type(
            &[float_rust_ty.clone(), float_rust_ty.clone()],
            float_rust_ty.clone(),
        );
        let outer_arg = "lhs".to_string();
        let inner_arg = "rhs".to_string();
        let inner_closure = Expr::Closure {
            params: vec![Param {
                name: inner_arg.clone(),
                ty: Some(float_rust_ty.clone()),
            }],
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(self.expr_call_path(
                    runtime_fn,
                    vec![
                        self.expr_clone(self.expr_path(outer_arg.clone())),
                        self.expr_path(inner_arg),
                    ],
                ))),
            },
            is_move: true,
        };
        let inner_callable_expr =
            self.callable_literal_expr(&float_ty, &float_ty, inner_closure)?;
        let outer_ret_ty = match self.local_type(body, 0) {
            Some(MirType::Fn(_, _, _, outer_ret))
            | Some(MirType::FnItem(_, _, _, _, outer_ret))
            | Some(MirType::Closure(_, _, _, _, outer_ret)) => outer_ret.as_ref(),
            _ => {
                return Err(TypedCodegenError::new(
                    "float builtin has invalid top-level function type",
                ))
            }
        };
        let outer_closure = Expr::Closure {
            params: vec![Param {
                name: outer_arg,
                ty: Some(float_rust_ty),
            }],
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(inner_callable_expr)),
            },
            is_move: true,
        };
        let outer_callable_expr =
            self.callable_literal_expr(&float_ty, outer_ret_ty, outer_closure)?;
        Ok(Some(Item::Fn {
            name: body.name.clone(),
            params: Vec::new(),
            ret: Some(ret_ty),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(outer_callable_expr)),
            },
        }))
    }

    fn emit_debug_print_builtin(
        &self,
        body: &TypedBody,
        name: &str,
        expected_arg: &MirType,
    ) -> Result<Option<Item>, TypedCodegenError> {
        if !self.unary_identity_builtin_signature_matches(body, expected_arg) {
            return Err(TypedCodegenError::new(format!(
                "print builtin '{}' must have type {} -> {}",
                name,
                self.rust_type(expected_arg)?,
                self.rust_type(expected_arg)?
            )));
        }

        let arg_ty = self.rust_type(expected_arg)?;
        let ret_ty = self.curried_fn_type(&[arg_ty.clone()], arg_ty.clone());
        let arg_name = "value".to_string();
        let print_stmt = Stmt::Expr(Expr::MacroCall {
            name: "println".to_string(),
            args: vec![self.expr_lit_str("{:?}"), self.expr_path(arg_name.clone())],
        });
        let closure = Expr::Closure {
            params: vec![Param {
                name: arg_name.clone(),
                ty: Some(arg_ty),
            }],
            body: Block {
                stmts: vec![print_stmt],
                tail: Some(Box::new(self.expr_path(arg_name))),
            },
            is_move: true,
        };
        let callable_expr = self.callable_literal_expr(expected_arg, expected_arg, closure)?;
        let body = Block {
            stmts: Vec::new(),
            tail: Some(Box::new(callable_expr)),
        };

        Ok(Some(Item::Fn {
            name: name.to_string(),
            params: Vec::new(),
            ret: Some(ret_ty),
            body,
        }))
    }

    fn emit_closure_adapter_fn(
        &self,
        body: &TypedBody,
        global_idx: usize,
    ) -> Result<Item, TypedCodegenError> {
        let captures = self.closure_capture_types(&body.body)?;
        if let Some(expected) = self
            .closure_usage
            .get(&global_idx)
            .and_then(|u| u.closure_capture_len)
        {
            if expected != captures.len() {
                return Err(TypedCodegenError::new(format!(
                    "closure_{} capture mismatch: expected {}, got {}",
                    global_idx,
                    expected,
                    captures.len()
                )));
            }
        }

        let arg_ty = self
            .local_type(body, 2)
            .ok_or_else(|| TypedCodegenError::new("missing closure arg"))?;
        let ret_ty = self
            .local_type(body, 0)
            .ok_or_else(|| TypedCodegenError::new("missing closure return type"))?;
        let mut generic_types: Vec<&MirType> = Vec::new();
        generic_types.extend(captures.iter());
        generic_types.push(arg_ty);
        generic_types.push(ret_ty);
        let generics = self.generics_for_types(generic_types);

        let mut call_args = Vec::new();
        for i in 0..captures.len() {
            call_args.push(self.expr_path(format!("cap.{}", i)));
        }
        call_args.push(self.expr_path("arg"));

        Ok(Item::Fn {
            name: self.fn_name_with_generics(&format!("closure_adapter_{}", global_idx), &generics),
            params: vec![
                Param {
                    name: "cap".to_string(),
                    ty: Some(self.capture_tuple_type(&captures)?),
                },
                Param {
                    name: "arg".to_string(),
                    ty: Some(self.rust_type(arg_ty)?),
                },
            ],
            ret: Some(self.rust_type(ret_ty)?),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(
                    self.expr_call(self.expr_path(body.name.clone()), call_args),
                )),
            },
        })
    }

    fn emit_fix_adapter_fn(
        &self,
        body: &TypedBody,
        global_idx: usize,
    ) -> Result<Item, TypedCodegenError> {
        let captures = self.closure_capture_types(&body.body)?;
        let explicit_captures = captures
            .get(1..)
            .ok_or_else(|| TypedCodegenError::new("fix closure missing self capture"))?;
        if let Some(expected) = self
            .closure_usage
            .get(&global_idx)
            .and_then(|u| u.fix_capture_len)
        {
            if expected != explicit_captures.len() {
                return Err(TypedCodegenError::new(format!(
                    "fix closure_{} capture mismatch: expected {}, got {}",
                    global_idx,
                    expected,
                    explicit_captures.len()
                )));
            }
        }

        let arg_ty = self
            .local_type(body, 2)
            .ok_or_else(|| TypedCodegenError::new("missing closure arg"))?;
        let ret_ty = self
            .local_type(body, 0)
            .ok_or_else(|| TypedCodegenError::new("missing closure return type"))?;
        let mut generic_types: Vec<&MirType> = Vec::new();
        generic_types.extend(explicit_captures.iter());
        generic_types.push(arg_ty);
        generic_types.push(ret_ty);
        let generics = self.generics_for_types(generic_types);

        let mut call_args = Vec::new();
        call_args.push(self.expr_path("self_fn"));
        for i in 0..explicit_captures.len() {
            call_args.push(self.expr_path(format!("cap.{}", i)));
        }
        call_args.push(self.expr_path("arg"));

        Ok(Item::Fn {
            name: self.fn_name_with_generics(&format!("fix_adapter_{}", global_idx), &generics),
            params: vec![
                Param {
                    name: "self_fn".to_string(),
                    ty: Some(self.callable_dyn_type(arg_ty, ret_ty)?),
                },
                Param {
                    name: "cap".to_string(),
                    ty: Some(self.capture_tuple_type(explicit_captures)?),
                },
                Param {
                    name: "arg".to_string(),
                    ty: Some(self.rust_type(arg_ty)?),
                },
            ],
            ret: Some(self.rust_type(ret_ty)?),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(
                    self.expr_call(self.expr_path(body.name.clone()), call_args),
                )),
            },
        })
    }

    fn unary_identity_builtin_signature_matches(
        &self,
        body: &TypedBody,
        expected_arg: &MirType,
    ) -> bool {
        let ty = match self.local_type(body, 0) {
            Some(ty) => ty,
            None => return false,
        };
        match ty {
            MirType::Fn(kind, _, args, ret)
            | MirType::FnItem(_, kind, _, args, ret)
            | MirType::Closure(kind, _, _, args, ret) => {
                let _ = kind;
                args.len() == 1 && args[0] == *expected_arg && **ret == *expected_arg
            }
            _ => false,
        }
    }

    fn binary_curried_identity_builtin_signature_matches(
        &self,
        body: &TypedBody,
        expected_arg: &MirType,
    ) -> bool {
        let ty = match self.local_type(body, 0) {
            Some(ty) => ty,
            None => return false,
        };
        match ty {
            MirType::Fn(_, _, outer_args, outer_ret)
            | MirType::FnItem(_, _, _, outer_args, outer_ret)
            | MirType::Closure(_, _, _, outer_args, outer_ret) => {
                if outer_args.len() != 1 || outer_args[0] != *expected_arg {
                    return false;
                }
                match outer_ret.as_ref() {
                    MirType::Fn(_, _, inner_args, inner_ret)
                    | MirType::FnItem(_, _, _, inner_args, inner_ret)
                    | MirType::Closure(_, _, _, inner_args, inner_ret) => {
                        inner_args.len() == 1
                            && inner_args[0] == *expected_arg
                            && inner_ret.as_ref() == expected_arg
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn write_file_builtin_signature_matches(&self, body: &TypedBody, text_ty: &MirType) -> bool {
        let ty = match self.local_type(body, 0) {
            Some(ty) => ty,
            None => return false,
        };
        match ty {
            MirType::Fn(_, _, outer_args, outer_ret)
            | MirType::FnItem(_, _, _, outer_args, outer_ret)
            | MirType::Closure(_, _, _, outer_args, outer_ret) => {
                if outer_args.len() != 1 || outer_args[0] != *text_ty {
                    return false;
                }
                match outer_ret.as_ref() {
                    MirType::Fn(_, _, inner_args, inner_ret)
                    | MirType::FnItem(_, _, _, inner_args, inner_ret)
                    | MirType::Closure(_, _, _, inner_args, inner_ret) => {
                        inner_args.len() == 1
                            && inner_args[0] == *text_ty
                            && inner_ret.as_ref() == text_ty
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn text_mir_type(&self) -> Option<MirType> {
        self.ids
            .adt_id("Text")
            .map(|adt_id| MirType::Adt(adt_id, Vec::new()))
    }

    fn int_mir_type(&self) -> Option<MirType> {
        self.ids
            .adt_id("Int")
            .map(|adt_id| MirType::Adt(adt_id, Vec::new()))
    }

    fn float_mir_type(&self) -> Option<MirType> {
        self.ids
            .adt_id("Float")
            .map(|adt_id| MirType::Adt(adt_id, Vec::new()))
    }

    fn adt_variant_tag_expr(&self, adt_id: &AdtId, value_name: &str) -> Option<Expr> {
        let layout = self.adt_layouts.get(adt_id)?;
        let adt_name = self.adt_name(adt_id).to_string();
        let mut arms = Vec::with_capacity(layout.variants.len());

        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            let ctor_id = CtorId::new(adt_id.clone(), variant_idx);
            let ctor_name = self.ctor_name_map.get(&ctor_id)?.clone();
            let path = format!("{}::{}", adt_name, ctor_name);
            let pat = if variant.fields.is_empty() {
                Pat::Path(path)
            } else {
                Pat::Tuple {
                    path,
                    args: vec![Pat::Wild; variant.fields.len()],
                }
            };
            arms.push(MatchArm {
                pat,
                body: Block {
                    stmts: Vec::new(),
                    tail: Some(Box::new(Expr::Lit(Lit::Str(ctor_name)))),
                },
            });
        }
        arms.push(MatchArm {
            pat: Pat::Wild,
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(Expr::Lit(Lit::Str("<value>".to_string())))),
            },
        });

        Some(Expr::Match {
            scrutinee: Box::new(Expr::Path(value_name.to_string())),
            arms,
        })
    }

    fn emit_main(&self, program: &TypedProgram) -> Result<Item, TypedCodegenError> {
        let mut stmts = Vec::new();
        if let Some(name) = &program.main_name {
            stmts.push(Stmt::Let {
                name: "result".to_string(),
                mutable: false,
                ty: None,
                value: Some(Expr::Call {
                    func: Box::new(Expr::Path(name.clone())),
                    args: Vec::new(),
                }),
            });
            let print_expr = match self.find_def_return_type(program, name) {
                Some(ty) if !self.is_fn_type(ty) => {
                    if matches!(ty, MirType::Nat | MirType::Bool) {
                        Expr::MacroCall {
                            name: "println".to_string(),
                            args: vec![
                                Expr::Lit(Lit::Str("Result: {}".to_string())),
                                Expr::Path("result".to_string()),
                            ],
                        }
                    } else if self.text_mir_type().as_ref() == Some(ty) {
                        Expr::MacroCall {
                            name: "println".to_string(),
                            args: vec![
                                Expr::Lit(Lit::Str("Result: {}".to_string())),
                                Expr::Call {
                                    func: Box::new(Expr::Path(
                                        "runtime_text_to_string".to_string(),
                                    )),
                                    args: vec![Expr::MethodCall {
                                        receiver: Box::new(Expr::Path("result".to_string())),
                                        method: "clone".to_string(),
                                        args: Vec::new(),
                                    }],
                                },
                            ],
                        }
                    } else if self.int_mir_type().as_ref() == Some(ty) {
                        Expr::MacroCall {
                            name: "println".to_string(),
                            args: vec![
                                Expr::Lit(Lit::Str("Result: {}".to_string())),
                                Expr::Call {
                                    func: Box::new(Expr::Path("runtime_int_to_string".to_string())),
                                    args: vec![Expr::MethodCall {
                                        receiver: Box::new(Expr::Path("result".to_string())),
                                        method: "clone".to_string(),
                                        args: Vec::new(),
                                    }],
                                },
                            ],
                        }
                    } else if self.float_mir_type().as_ref() == Some(ty) {
                        Expr::MacroCall {
                            name: "println".to_string(),
                            args: vec![
                                Expr::Lit(Lit::Str("Result: {}".to_string())),
                                Expr::Call {
                                    func: Box::new(Expr::Path(
                                        "runtime_float_to_string".to_string(),
                                    )),
                                    args: vec![Expr::MethodCall {
                                        receiver: Box::new(Expr::Path("result".to_string())),
                                        method: "clone".to_string(),
                                        args: Vec::new(),
                                    }],
                                },
                            ],
                        }
                    } else if let MirType::Adt(adt_id, _args) = ty {
                        if let Some(tag_expr) = self.adt_variant_tag_expr(adt_id, "result") {
                            Expr::MacroCall {
                                name: "println".to_string(),
                                args: vec![Expr::Lit(Lit::Str("Result: {}".to_string())), tag_expr],
                            }
                        } else {
                            Expr::MacroCall {
                                name: "println".to_string(),
                                args: vec![Expr::Lit(Lit::Str("Result: <value>".to_string()))],
                            }
                        }
                    } else {
                        Expr::MacroCall {
                            name: "println".to_string(),
                            args: vec![Expr::Lit(Lit::Str("Result: <value>".to_string()))],
                        }
                    }
                }
                _ => Expr::MacroCall {
                    name: "println".to_string(),
                    args: vec![Expr::Lit(Lit::Str("Result: <func>".to_string()))],
                },
            };
            stmts.push(Stmt::Expr(print_expr));
        }
        Ok(Item::Fn {
            name: "main".to_string(),
            params: Vec::new(),
            ret: None,
            body: Block { stmts, tail: None },
        })
    }

    fn emit_nat_recursor(&self, spec: &RecursorSpec) -> Result<Vec<Item>, TypedCodegenError> {
        let args = &spec.arg_types;
        if args.len() != 4 {
            return Err(TypedCodegenError::new(format!(
                "Nat recursor expects 4 args, got {}",
                args.len()
            )));
        }
        let mut rec_types: Vec<&MirType> = args.iter().collect();
        rec_types.push(&spec.result_ty);
        let generics = self.generics_for_types(rec_types);

        let motive_ty = self.rust_type(&args[0])?;
        let zero_ty = self.rust_type(&args[1])?;
        let succ_ty = self.rust_type(&args[2])?;
        let major_ty = self.rust_type(&args[3])?;
        let ret_ty = self.rust_type(&spec.result_ty)?;

        let entry_ret_ty = self.curried_fn_type(
            &[zero_ty.clone(), succ_ty.clone(), major_ty.clone()],
            ret_ty.clone(),
        );
        let arg_names = vec![
            "zero_case".to_string(),
            "succ_case".to_string(),
            "n_val".to_string(),
        ];
        let arg_types = vec![zero_ty.clone(), succ_ty.clone(), major_ty.clone()];
        let impl_call = self.expr_call(
            self.expr_path(spec.impl_name()),
            vec![
                self.expr_clone(self.expr_path("motive")),
                self.expr_clone(self.expr_path("zero_case")),
                self.expr_clone(self.expr_path("succ_case")),
                self.expr_path("n_val"),
            ],
        );
        let entry_expr = self.curried_entry_expr(
            &arg_names,
            &arg_types,
            &["motive".to_string()],
            &impl_call,
            &ret_ty,
        );
        let entry_item = Item::Fn {
            name: self.fn_name_with_generics(&spec.name, &generics),
            params: vec![Param {
                name: "motive".to_string(),
                ty: Some(motive_ty.clone()),
            }],
            ret: Some(entry_ret_ty),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(entry_expr)),
            },
        };

        let mut stmts = Vec::new();
        stmts.push(Stmt::Let {
            name: "_".to_string(),
            mutable: false,
            ty: None,
            value: Some(Expr::Ref {
                mutable: false,
                expr: Box::new(self.expr_path("motive")),
            }),
        });
        let then_block = Block {
            stmts: Vec::new(),
            tail: Some(Box::new(self.expr_path("zero_case"))),
        };
        let mut else_stmts = Vec::new();
        else_stmts.push(Stmt::Let {
            name: "n_prev".to_string(),
            mutable: false,
            ty: None,
            value: Some(Expr::Binary {
                op: BinaryOp::Sub,
                left: Box::new(self.expr_path("n_val")),
                right: Box::new(self.expr_lit_int("1")),
            }),
        });
        else_stmts.push(Stmt::Let {
            name: "ih".to_string(),
            mutable: false,
            ty: None,
            value: Some(self.expr_call(
                self.expr_path(spec.impl_name()),
                vec![
                    self.expr_clone(self.expr_path("motive")),
                    self.expr_clone(self.expr_path("zero_case")),
                    self.expr_clone(self.expr_path("succ_case")),
                    self.expr_path("n_prev"),
                ],
            )),
        });
        else_stmts.push(Stmt::Let {
            name: "res1".to_string(),
            mutable: false,
            ty: None,
            value: Some(
                self.expr_call_callable(self.expr_path("succ_case"), self.expr_path("n_prev")),
            ),
        });
        else_stmts.push(Stmt::Let {
            name: "res2".to_string(),
            mutable: false,
            ty: None,
            value: Some(self.expr_call_callable(self.expr_path("res1"), self.expr_path("ih"))),
        });
        let else_block = Block {
            stmts: else_stmts,
            tail: Some(Box::new(self.expr_path("res2"))),
        };
        let if_expr = Expr::If {
            cond: Box::new(Expr::Binary {
                op: BinaryOp::Eq,
                left: Box::new(self.expr_path("n_val")),
                right: Box::new(self.expr_lit_int("0")),
            }),
            then_branch: then_block,
            else_branch: Some(else_block),
        };
        let impl_item = Item::Fn {
            name: self.fn_name_with_generics(&spec.impl_name(), &generics),
            params: vec![
                Param {
                    name: "motive".to_string(),
                    ty: Some(motive_ty),
                },
                Param {
                    name: "zero_case".to_string(),
                    ty: Some(zero_ty),
                },
                Param {
                    name: "succ_case".to_string(),
                    ty: Some(succ_ty),
                },
                Param {
                    name: "n_val".to_string(),
                    ty: Some(major_ty),
                },
            ],
            ret: Some(ret_ty),
            body: Block {
                stmts,
                tail: Some(Box::new(if_expr)),
            },
        };

        Ok(vec![entry_item, impl_item])
    }

    fn emit_bool_recursor(&self, spec: &RecursorSpec) -> Result<Vec<Item>, TypedCodegenError> {
        let args = &spec.arg_types;
        if args.len() != 4 {
            return Err(TypedCodegenError::new(format!(
                "Bool recursor expects 4 args, got {}",
                args.len()
            )));
        }
        let mut rec_types: Vec<&MirType> = args.iter().collect();
        rec_types.push(&spec.result_ty);
        let generics = self.generics_for_types(rec_types);

        let motive_ty = self.rust_type(&args[0])?;
        let true_ty = self.rust_type(&args[1])?;
        let false_ty = self.rust_type(&args[2])?;
        let major_ty = self.rust_type(&args[3])?;
        let ret_ty = self.rust_type(&spec.result_ty)?;

        let entry_ret_ty = self.curried_fn_type(
            &[true_ty.clone(), false_ty.clone(), major_ty.clone()],
            ret_ty.clone(),
        );
        let arg_names = vec![
            "true_case".to_string(),
            "false_case".to_string(),
            "b_val".to_string(),
        ];
        let arg_types = vec![true_ty.clone(), false_ty.clone(), major_ty.clone()];
        let impl_call = self.expr_call(
            self.expr_path(spec.impl_name()),
            vec![
                self.expr_clone(self.expr_path("motive")),
                self.expr_path("true_case"),
                self.expr_path("false_case"),
                self.expr_path("b_val"),
            ],
        );
        let entry_expr = self.curried_entry_expr(
            &arg_names,
            &arg_types,
            &["motive".to_string()],
            &impl_call,
            &ret_ty,
        );
        let entry_item = Item::Fn {
            name: self.fn_name_with_generics(&spec.name, &generics),
            params: vec![Param {
                name: "motive".to_string(),
                ty: Some(motive_ty.clone()),
            }],
            ret: Some(entry_ret_ty),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(entry_expr)),
            },
        };

        let mut stmts = Vec::new();
        stmts.push(Stmt::Let {
            name: "_".to_string(),
            mutable: false,
            ty: None,
            value: Some(Expr::Ref {
                mutable: false,
                expr: Box::new(self.expr_path("motive")),
            }),
        });
        let then_block = Block {
            stmts: Vec::new(),
            tail: Some(Box::new(self.expr_path("true_case"))),
        };
        let else_block = Block {
            stmts: Vec::new(),
            tail: Some(Box::new(self.expr_path("false_case"))),
        };
        let if_expr = Expr::If {
            cond: Box::new(self.expr_path("b_val")),
            then_branch: then_block,
            else_branch: Some(else_block),
        };
        let impl_item = Item::Fn {
            name: self.fn_name_with_generics(&spec.impl_name(), &generics),
            params: vec![
                Param {
                    name: "motive".to_string(),
                    ty: Some(motive_ty),
                },
                Param {
                    name: "true_case".to_string(),
                    ty: Some(true_ty),
                },
                Param {
                    name: "false_case".to_string(),
                    ty: Some(false_ty),
                },
                Param {
                    name: "b_val".to_string(),
                    ty: Some(major_ty),
                },
            ],
            ret: Some(ret_ty),
            body: Block {
                stmts,
                tail: Some(Box::new(if_expr)),
            },
        };

        Ok(vec![entry_item, impl_item])
    }

    fn emit_adt_recursor(&self, spec: &RecursorSpec) -> Result<Vec<Item>, TypedCodegenError> {
        let args = &spec.arg_types;
        let mut rec_types: Vec<&MirType> = args.iter().collect();
        rec_types.push(&spec.result_ty);
        let generics = self.generics_for_types(rec_types);
        let adt_name = self.adt_name(&spec.adt_id);
        let Some(layout) = self.adt_layouts.get(&spec.adt_id) else {
            return Err(TypedCodegenError::new("missing ADT layout"));
        };
        let decl =
            self.env.inductives.get(spec.adt_id.name()).ok_or_else(|| {
                TypedCodegenError::new("missing inductive declaration for recursor")
            })?;
        let param_count = decl.num_params;
        let index_count = count_indices(&decl.ty, decl.num_params);
        let expected = param_count + 1 + layout.variants.len() + index_count + 1;
        if args.len() != expected {
            return Err(TypedCodegenError::new(format!(
                "recursor for {} expects {} args, got {}",
                adt_name,
                expected,
                args.len()
            )));
        }

        let motive_pos = param_count;
        let minor_start = motive_pos + 1;
        let minor_end = minor_start + layout.variants.len();
        let index_start = minor_end;
        let index_end = index_start + index_count;
        let major_pos = index_end;

        let param_types: Vec<String> = args[..param_count]
            .iter()
            .map(|ty| self.rust_type(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let motive_ty = self.rust_type(&args[motive_pos])?;
        let major_ty = self.rust_type(&args[major_pos])?;
        let ret_ty = self.rust_type(&spec.result_ty)?;
        let minor_types: Vec<String> = args[minor_start..minor_end]
            .iter()
            .map(|ty| self.rust_type(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let index_types: Vec<String> = args[index_start..index_end]
            .iter()
            .map(|ty| self.rust_type(ty))
            .collect::<Result<Vec<_>, _>>()?;

        let mut all_arg_names = Vec::new();
        let mut all_arg_types = Vec::new();
        for (idx, ty) in param_types.iter().enumerate() {
            all_arg_names.push(format!("param_{}", idx));
            all_arg_types.push(ty.clone());
        }
        all_arg_names.push("motive".to_string());
        all_arg_types.push(motive_ty.clone());
        for (idx, ty) in minor_types.iter().enumerate() {
            all_arg_names.push(format!("minor_{}", idx));
            all_arg_types.push(ty.clone());
        }
        for (idx, ty) in index_types.iter().enumerate() {
            all_arg_names.push(format!("index_{}", idx));
            all_arg_types.push(ty.clone());
        }
        all_arg_names.push("major".to_string());
        all_arg_types.push(major_ty.clone());

        let entry_first_name = all_arg_names
            .first()
            .ok_or_else(|| TypedCodegenError::new("recursor requires at least one argument"))?
            .clone();
        let entry_first_ty = all_arg_types
            .first()
            .ok_or_else(|| TypedCodegenError::new("recursor requires at least one argument"))?
            .clone();
        let entry_ret_ty = self.curried_fn_type(&all_arg_types[1..], ret_ty.clone());

        let captured_names = vec![entry_first_name.clone()];
        let impl_call = self.expr_call(self.expr_path(spec.impl_name()), {
            let mut args = Vec::new();
            for idx in 0..param_count {
                args.push(self.expr_clone(self.expr_path(format!("param_{}", idx))));
            }
            args.push(self.expr_clone(self.expr_path("motive")));
            for idx in 0..minor_types.len() {
                args.push(self.expr_path(format!("minor_{}", idx)));
            }
            for idx in 0..index_types.len() {
                args.push(self.expr_path(format!("index_{}", idx)));
            }
            args.push(self.expr_path("major"));
            args
        });
        let entry_expr = if all_arg_names.len() == 1 {
            impl_call
        } else {
            self.curried_entry_expr(
                &all_arg_names[1..],
                &all_arg_types[1..],
                &captured_names,
                &impl_call,
                &ret_ty,
            )
        };
        let entry_item = Item::Fn {
            name: self.fn_name_with_generics(&spec.name, &generics),
            params: vec![Param {
                name: entry_first_name,
                ty: Some(entry_first_ty),
            }],
            ret: Some(entry_ret_ty),
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(entry_expr)),
            },
        };

        let mut stmts = Vec::new();
        stmts.push(Stmt::Let {
            name: "_".to_string(),
            mutable: false,
            ty: None,
            value: Some(Expr::Ref {
                mutable: false,
                expr: Box::new(self.expr_path("motive")),
            }),
        });

        let mut arms = Vec::new();
        for (variant_idx, variant) in layout.variants.iter().enumerate() {
            let ctor_name = self
                .ctor_name_map
                .get(&variant.ctor)
                .cloned()
                .unwrap_or_else(|| format!("Ctor{}", variant_idx));
            let pat = if variant.fields.is_empty() {
                Pat::Path(format!("{}::{}", adt_name, ctor_name))
            } else {
                let args = (0..variant.fields.len())
                    .map(|idx| Pat::Bind(format!("field_{}", idx)))
                    .collect::<Vec<_>>();
                Pat::Tuple {
                    path: format!("{}::{}", adt_name, ctor_name),
                    args,
                }
            };

            let mut arm_stmts = Vec::new();
            let mut arg_exprs = Vec::new();
            for (field_idx, field_ty) in variant.fields.iter().enumerate() {
                let field_name = format!("field_{}", field_idx);
                if self
                    .boxed_fields
                    .contains(&(spec.adt_id.clone(), variant_idx, field_idx))
                {
                    arm_stmts.push(Stmt::Let {
                        name: field_name.clone(),
                        mutable: false,
                        ty: None,
                        value: Some(self.expr_clone(Expr::Unary {
                            op: UnaryOp::Deref,
                            expr: Box::new(self.expr_path(&field_name)),
                        })),
                    });
                }
                arg_exprs.push(self.expr_path(&field_name));

                if self.is_direct_recursive(field_ty, &spec.adt_id) {
                    let ih_name = format!("ih_{}", field_idx);
                    let mut ih_args = Vec::new();
                    for idx in 0..param_count {
                        ih_args.push(self.expr_clone(self.expr_path(format!("param_{}", idx))));
                    }
                    ih_args.push(self.expr_clone(self.expr_path("motive")));
                    for idx in 0..minor_types.len() {
                        ih_args.push(self.expr_clone(self.expr_path(format!("minor_{}", idx))));
                    }
                    for idx in 0..index_types.len() {
                        ih_args.push(self.expr_clone(self.expr_path(format!("index_{}", idx))));
                    }
                    ih_args.push(self.expr_clone(self.expr_path(&field_name)));
                    arm_stmts.push(Stmt::Let {
                        name: ih_name.clone(),
                        mutable: false,
                        ty: None,
                        value: Some(self.expr_call(self.expr_path(spec.impl_name()), ih_args)),
                    });
                    arg_exprs.push(self.expr_path(ih_name));
                }
            }

            let tail = if arg_exprs.is_empty() {
                self.expr_path(format!("minor_{}", variant_idx))
            } else {
                arm_stmts.push(Stmt::Let {
                    name: "current".to_string(),
                    mutable: false,
                    ty: None,
                    value: Some(self.expr_path(format!("minor_{}", variant_idx))),
                });
                for arg in arg_exprs {
                    arm_stmts.push(Stmt::Let {
                        name: "current".to_string(),
                        mutable: false,
                        ty: None,
                        value: Some(self.expr_call_callable(self.expr_path("current"), arg)),
                    });
                }
                self.expr_path("current")
            };

            arms.push(MatchArm {
                pat,
                body: Block {
                    stmts: arm_stmts,
                    tail: Some(Box::new(tail)),
                },
            });
        }
        arms.push(MatchArm {
            pat: Pat::Wild,
            body: Block {
                stmts: Vec::new(),
                tail: Some(Box::new(self.expr_unreachable())),
            },
        });

        let match_expr = Expr::Match {
            scrutinee: Box::new(self.expr_path("major")),
            arms,
        };

        let impl_item = Item::Fn {
            name: self.fn_name_with_generics(&spec.impl_name(), &generics),
            params: {
                let mut params = Vec::new();
                for (idx, ty) in param_types.iter().enumerate() {
                    params.push(Param {
                        name: format!("param_{}", idx),
                        ty: Some(ty.clone()),
                    });
                }
                params.push(Param {
                    name: "motive".to_string(),
                    ty: Some(motive_ty),
                });
                for (idx, ty) in minor_types.iter().enumerate() {
                    params.push(Param {
                        name: format!("minor_{}", idx),
                        ty: Some(ty.clone()),
                    });
                }
                for (idx, ty) in index_types.iter().enumerate() {
                    params.push(Param {
                        name: format!("index_{}", idx),
                        ty: Some(ty.clone()),
                    });
                }
                params.push(Param {
                    name: "major".to_string(),
                    ty: Some(major_ty),
                });
                params
            },
            ret: Some(ret_ty),
            body: Block {
                stmts,
                tail: Some(Box::new(match_expr)),
            },
        };

        Ok(vec![entry_item, impl_item])
    }

    fn curried_entry_expr(
        &self,
        arg_names: &[String],
        arg_types: &[String],
        captured: &[String],
        final_expr: &Expr,
        final_ret_ty: &str,
    ) -> Expr {
        if arg_names.is_empty() {
            return final_expr.clone();
        }
        self.curried_entry_level(0, arg_names, arg_types, captured, final_expr, final_ret_ty)
    }

    fn curried_entry_level(
        &self,
        level: usize,
        arg_names: &[String],
        arg_types: &[String],
        captured: &[String],
        final_expr: &Expr,
        final_ret_ty: &str,
    ) -> Expr {
        let arg_name = &arg_names[level];
        let arg_type = &arg_types[level];
        let mut stmts = Vec::new();
        for name in captured {
            stmts.push(Stmt::Let {
                name: name.clone(),
                mutable: false,
                ty: None,
                value: Some(self.expr_clone(self.expr_path(name))),
            });
        }
        let mut next_captured = captured.to_vec();
        next_captured.push(arg_name.clone());
        let tail = if level + 1 == arg_names.len() {
            final_expr.clone()
        } else {
            self.curried_entry_level(
                level + 1,
                arg_names,
                arg_types,
                &next_captured,
                final_expr,
                final_ret_ty,
            )
        };
        let closure = Expr::Closure {
            params: vec![Param {
                name: arg_name.clone(),
                ty: Some(arg_type.clone()),
            }],
            body: Block {
                stmts,
                tail: Some(Box::new(tail)),
            },
            is_move: true,
        };
        let tail_ty = if level + 1 == arg_names.len() {
            final_ret_ty.to_string()
        } else {
            self.curried_fn_type(&arg_types[level + 1..], final_ret_ty.to_string())
        };
        Expr::Block(Block {
            stmts: vec![Stmt::Let {
                name: "__curried".to_string(),
                mutable: false,
                ty: Some(format!(
                    "Rc<dyn LrlCallable<{}, {}>>",
                    arg_type.clone(),
                    tail_ty
                )),
                value: Some(self.expr_call_path("Rc::new", vec![closure])),
            }],
            tail: Some(Box::new(self.expr_path("__curried"))),
        })
    }

    fn curried_fn_type(&self, arg_types: &[String], ret_ty: String) -> String {
        let mut result = ret_ty;
        for arg in arg_types.iter().rev() {
            result = format!("Rc<dyn LrlCallable<{}, {}>>", arg, result);
        }
        result
    }

    fn finalize_recursors(&mut self) -> Result<(), TypedCodegenError> {
        if self.recursor_sigs.is_empty() {
            return Ok(());
        }
        let mut keys: Vec<_> = self.recursor_sigs.keys().cloned().collect();
        keys.sort_by(|(a_id, a_key), (b_id, b_key)| {
            let name_cmp = self.adt_name(a_id).cmp(self.adt_name(b_id));
            if name_cmp == std::cmp::Ordering::Equal {
                a_key.cmp(b_key)
            } else {
                name_cmp
            }
        });

        let mut per_adt_count: HashMap<AdtId, usize> = HashMap::new();
        for (adt_id, type_key) in keys {
            let sig = self
                .recursor_sigs
                .get(&(adt_id.clone(), type_key.clone()))
                .ok_or_else(|| TypedCodegenError::new("missing recursor signature"))?
                .clone();
            let count = per_adt_count.entry(adt_id.clone()).or_insert(0);
            let fn_name = format!("rec_{}_entry_{}", self.adt_name(&adt_id), *count);
            *count += 1;
            self.recursor_lookup
                .insert((adt_id.clone(), type_key.clone()), fn_name.clone());
            self.recursor_specs.push(RecursorSpec {
                adt_id,
                arg_types: sig.arg_types,
                result_ty: sig.result_ty,
                name: fn_name,
            });
        }

        Ok(())
    }

    fn record_recursor_signature(
        &mut self,
        body: &TypedBody,
        place: &Place,
        ind_name: &str,
        used_adts: &mut HashSet<AdtId>,
    ) -> Result<(), TypedCodegenError> {
        let adt_id = self.check_recursor_supported(ind_name)?;
        let local_ty = self.local_type(body, place.local.index()).ok_or_else(|| {
            TypedCodegenError::new(format!("missing recursor type in {}", body.name))
        })?;
        let expected_args = self.expected_recursor_args(ind_name)?;
        let (arg_types, result_ty) = match self.split_fn_chain(local_ty, expected_args) {
            Some(result) => result,
            None => {
                let actual = self
                    .peel_fn_chain(local_ty)
                    .map(|(args, _)| args.len())
                    .unwrap_or(0);
                return Err(TypedCodegenError::new(format!(
                    "recursor for {} expects at least {} args, got {}",
                    ind_name, expected_args, actual
                )));
            }
        };
        if arg_types.len() != expected_args {
            return Err(TypedCodegenError::new(format!(
                "recursor for {} expects {} args, got {}",
                ind_name,
                expected_args,
                arg_types.len()
            )));
        }

        let type_key = self.type_key(local_ty);
        self.recursor_sigs
            .entry((adt_id.clone(), type_key.clone()))
            .or_insert_with(|| RecursorSignature {
                arg_types: arg_types.clone(),
                result_ty: result_ty.clone(),
            });

        used_adts.insert(adt_id);
        Ok(())
    }

    fn expected_recursor_args(&self, ind_name: &str) -> Result<usize, TypedCodegenError> {
        let decl = self
            .env
            .inductives
            .get(ind_name)
            .ok_or_else(|| TypedCodegenError::new("unknown inductive in recursor"))?;
        let indices = count_indices(&decl.ty, decl.num_params);
        Ok(decl.num_params + 1 + decl.ctors.len() + indices + 1)
    }

    fn recursor_expr(
        &self,
        ind_name: &str,
        expected_ty: Option<&MirType>,
    ) -> Result<Expr, TypedCodegenError> {
        let adt_id = self.check_recursor_supported(ind_name)?;
        let candidates: Vec<_> = self
            .recursor_lookup
            .keys()
            .filter(|(id, _)| id == &adt_id)
            .cloned()
            .collect();

        let key = if let Some(ty) = expected_ty {
            (adt_id.clone(), self.type_key(ty))
        } else if candidates.len() == 1 {
            candidates[0].clone()
        } else {
            return Err(TypedCodegenError::new(format!(
                "ambiguous recursor for {}; expected type required",
                ind_name
            )));
        };

        let name = self.recursor_lookup.get(&key).ok_or_else(|| {
            TypedCodegenError::new(format!("missing recursor specialization for {}", ind_name))
        })?;

        Ok(self.expr_call(
            self.expr_path("Rc::new"),
            vec![self.expr_path(name.clone())],
        ))
    }

    fn check_recursor_supported(&self, ind_name: &str) -> Result<AdtId, TypedCodegenError> {
        let _decl = self.env.inductives.get(ind_name).ok_or_else(|| {
            TypedCodegenError::new(format!("unknown inductive in recursor: {}", ind_name))
        })?;
        Ok(self
            .ids
            .adt_id(ind_name)
            .unwrap_or_else(|| AdtId::new(ind_name)))
    }

    fn peel_fn_chain(&self, ty: &MirType) -> Option<(Vec<MirType>, MirType)> {
        let mut args = Vec::new();
        let mut current = ty;
        loop {
            match current {
                MirType::Fn(_, _, arg, ret)
                | MirType::FnItem(_, _, _, arg, ret)
                | MirType::Closure(_, _, _, arg, ret) => {
                    if arg.len() != 1 {
                        return None;
                    }
                    args.push(arg[0].clone());
                    current = ret;
                }
                _ => break,
            }
        }
        Some((args, current.clone()))
    }

    fn split_fn_chain(&self, ty: &MirType, arg_count: usize) -> Option<(Vec<MirType>, MirType)> {
        let mut args = Vec::new();
        let mut current = ty;
        for _ in 0..arg_count {
            match current {
                MirType::Fn(_, _, arg, ret)
                | MirType::FnItem(_, _, _, arg, ret)
                | MirType::Closure(_, _, _, arg, ret) => {
                    if arg.len() != 1 {
                        return None;
                    }
                    args.push(arg[0].clone());
                    current = ret;
                }
                _ => return None,
            }
        }
        Some((args, current.clone()))
    }

    fn type_key(&self, ty: &MirType) -> String {
        format!("{:?}", ty)
    }

    fn find_def_return_type<'b>(
        &self,
        program: &'b TypedProgram,
        name: &str,
    ) -> Option<&'b MirType> {
        program
            .defs
            .iter()
            .find(|body| body.name == *name)
            .and_then(|body| body.body.local_decls.get(0))
            .map(|decl| &decl.ty)
    }

    fn emit_body(&self, body: &TypedBody, is_closure: bool) -> Result<Item, TypedCodegenError> {
        let generics = self.body_generics(body);
        let bound_generics = self.body_generic_indices(body);
        let used_locals = self.collect_used_local_indices(&body.body);
        let ret_ty = self.rust_type(
            self.local_type(body, 0)
                .ok_or_else(|| TypedCodegenError::new("missing return type"))?,
        )?;

        let mut params = Vec::new();
        let mut closure_env = None;

        if is_closure {
            let captures = self.closure_capture_types(&body.body)?;
            let arg_ty = self.rust_type(
                self.local_type(body, 2)
                    .ok_or_else(|| TypedCodegenError::new("missing closure arg"))?,
            )?;
            for (i, cap_ty) in captures.iter().enumerate() {
                let cap_name = format!("__cap{}", i);
                let cap_ty_str = self.rust_type(cap_ty)?;
                params.push(Param {
                    name: cap_name.clone(),
                    ty: Some(cap_ty_str),
                });
            }
            params.push(Param {
                name: "__arg".to_string(),
                ty: Some(arg_ty),
            });
            closure_env = Some(ClosureEnv {
                capture_names: (0..captures.len()).map(|i| format!("__cap{}", i)).collect(),
            });
        } else if body.body.arg_count != 0 {
            return Err(TypedCodegenError::new(format!(
                "expected zero-arg body for {}, got {} args",
                body.name, body.body.arg_count
            )));
        }

        let mut stmts = Vec::new();
        stmts.push(Stmt::Let {
            name: "state".to_string(),
            mutable: true,
            ty: Some("usize".to_string()),
            value: Some(self.expr_lit_int("0")),
        });
        stmts.push(Stmt::Let {
            name: "_0".to_string(),
            mutable: true,
            ty: self.option_local_type_annotation_with_usage(
                0,
                self.local_type(body, 0)
                    .ok_or_else(|| TypedCodegenError::new("missing return type"))?,
                &bound_generics,
                &used_locals,
            )?,
            value: Some(self.expr_none()),
        });

        if is_closure {
            stmts.push(Stmt::Let {
                name: "_1".to_string(),
                mutable: true,
                ty: Some("std::option::Option<()>".to_string()),
                value: Some(self.expr_none()),
            });
            let arg_ty = self
                .local_type(body, 2)
                .ok_or_else(|| TypedCodegenError::new("missing closure arg"))?;
            stmts.push(Stmt::Let {
                name: "_2".to_string(),
                mutable: true,
                ty: self.option_local_type_annotation_with_usage(
                    2,
                    arg_ty,
                    &bound_generics,
                    &used_locals,
                )?,
                value: Some(self.expr_some(self.expr_path("__arg"))),
            });
            for i in 3..body.body.local_decls.len() {
                let local_ty = self
                    .local_type(body, i)
                    .ok_or_else(|| TypedCodegenError::new("missing local"))?;
                stmts.push(Stmt::Let {
                    name: format!("_{}", i),
                    mutable: true,
                    ty: self.option_local_type_annotation_with_usage(
                        i,
                        local_ty,
                        &bound_generics,
                        &used_locals,
                    )?,
                    value: Some(self.expr_none()),
                });
            }
        } else {
            for i in 1..body.body.local_decls.len() {
                let local_ty = self
                    .local_type(body, i)
                    .ok_or_else(|| TypedCodegenError::new("missing local"))?;
                stmts.push(Stmt::Let {
                    name: format!("_{}", i),
                    mutable: true,
                    ty: self.option_local_type_annotation_with_usage(
                        i,
                        local_ty,
                        &bound_generics,
                        &used_locals,
                    )?,
                    value: Some(self.expr_none()),
                });
            }
        }

        let mut arms = Vec::new();
        for (idx, block) in body.body.basic_blocks.iter().enumerate() {
            let mut block_stmts = Vec::new();
            for stmt in &block.statements {
                if let Some(stmt) = self.emit_statement(body, stmt, closure_env.as_ref())? {
                    block_stmts.push(stmt);
                }
            }
            if let Some(term) = &block.terminator {
                block_stmts.extend(self.emit_terminator(body, term, closure_env.as_ref())?);
            }
            arms.push(MatchArm {
                pat: Pat::Lit(Lit::Int(idx.to_string())),
                body: Block {
                    stmts: block_stmts,
                    tail: None,
                },
            });
        }
        arms.push(MatchArm {
            pat: Pat::Wild,
            body: Block {
                stmts: vec![Stmt::Break],
                tail: None,
            },
        });

        let match_expr = Expr::Match {
            scrutinee: Box::new(self.expr_path("state")),
            arms,
        };
        stmts.push(Stmt::Loop(Block {
            stmts: vec![Stmt::Expr(match_expr)],
            tail: None,
        }));

        let tail = Some(Box::new(
            self.expr_expect(self.expr_path("_0"), "return value not set"),
        ));

        Ok(Item::Fn {
            name: self.fn_name_with_generics(&body.name, &generics),
            params,
            ret: Some(ret_ty),
            body: Block { stmts, tail },
        })
    }

    fn emit_statement(
        &self,
        body: &TypedBody,
        stmt: &Statement,
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Option<Stmt>, TypedCodegenError> {
        match stmt {
            Statement::Assign(place, rvalue) => {
                if !place.projection.is_empty() {
                    return Err(TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedProjectionAssignment,
                        format!("assignment to projection is not supported in {}", body.name),
                    ));
                }
                let dest = self.expr_path(format!("_{}", place.local.index()));
                let expected_ty = self.place_type(body, place);
                let expr = self.rvalue_expr(body, rvalue, closure_env, expected_ty.as_ref())?;
                Ok(Some(Stmt::Assign {
                    target: dest,
                    value: self.expr_some(expr),
                }))
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => Ok(None),
            Statement::RuntimeCheck(check) => {
                Ok(Some(self.emit_runtime_check(body, check, closure_env)?))
            }
        }
    }

    fn emit_runtime_check(
        &self,
        body: &TypedBody,
        check: &RuntimeCheckKind,
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Stmt, TypedCodegenError> {
        let expr = match check {
            RuntimeCheckKind::RefCellBorrow { local } => self.expr_call_path(
                "runtime_refcell_borrow_check",
                vec![self.place_expr(body, &Place::from(*local), AccessKind::Copy, closure_env)?],
            ),
            RuntimeCheckKind::MutexLock { local } => self.expr_call_path(
                "runtime_mutex_lock",
                vec![self.place_expr(body, &Place::from(*local), AccessKind::Copy, closure_env)?],
            ),
            RuntimeCheckKind::BoundsCheck { local, index } => self.expr_call_path(
                "runtime_bounds_check",
                vec![
                    self.place_expr(body, &Place::from(*local), AccessKind::Copy, closure_env)?,
                    self.place_expr(body, &Place::from(*index), AccessKind::Copy, closure_env)?,
                ],
            ),
        };
        Ok(Stmt::Expr(expr))
    }

    fn emit_terminator(
        &self,
        body: &TypedBody,
        term: &Terminator,
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Vec<Stmt>, TypedCodegenError> {
        let mut stmts = Vec::new();
        match term {
            Terminator::Return => {
                stmts.push(Stmt::Break);
            }
            Terminator::Goto { target } => {
                stmts.push(Stmt::Assign {
                    target: self.expr_path("state"),
                    value: self.expr_lit_int(target.index().to_string()),
                });
                stmts.push(Stmt::Continue);
            }
            Terminator::SwitchInt { discr, targets } => {
                let discr_expr = self.operand_expr(body, discr, closure_env, None)?;
                let scrutinee = Expr::Cast {
                    expr: Box::new(discr_expr),
                    ty: "u128".to_string(),
                };
                let mut arms = Vec::new();
                for (idx, val) in targets.values.iter().enumerate() {
                    let target = targets.targets[idx];
                    arms.push(MatchArm {
                        pat: Pat::Lit(Lit::Int(val.to_string())),
                        body: Block {
                            stmts: vec![
                                Stmt::Assign {
                                    target: self.expr_path("state"),
                                    value: self.expr_lit_int(target.index().to_string()),
                                },
                                Stmt::Continue,
                            ],
                            tail: None,
                        },
                    });
                }
                if targets.targets.len() > targets.values.len() {
                    let default_target = targets.targets.last().unwrap();
                    arms.push(MatchArm {
                        pat: Pat::Wild,
                        body: Block {
                            stmts: vec![
                                Stmt::Assign {
                                    target: self.expr_path("state"),
                                    value: self.expr_lit_int(default_target.index().to_string()),
                                },
                                Stmt::Continue,
                            ],
                            tail: None,
                        },
                    });
                } else {
                    arms.push(MatchArm {
                        pat: Pat::Wild,
                        body: Block {
                            stmts: vec![Stmt::Expr(self.expr_unreachable())],
                            tail: None,
                        },
                    });
                }
                stmts.push(Stmt::Expr(Expr::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                }));
            }
            Terminator::Call {
                func,
                args,
                destination,
                target,
            } => {
                let func_expr = self.call_operand_expr(body, func, closure_env)?;
                let arg_expr = if let Some(arg) = args.get(0) {
                    self.operand_expr(body, arg, closure_env, None)?
                } else {
                    self.expr_path("()")
                };
                let call_expr = self.expr_call_callable(func_expr, arg_expr);
                let dest = self.expr_path(format!("_{}", destination.local.index()));
                stmts.push(Stmt::Assign {
                    target: dest,
                    value: self.expr_some(call_expr),
                });
                if let Some(next) = target {
                    stmts.push(Stmt::Assign {
                        target: self.expr_path("state"),
                        value: self.expr_lit_int(next.index().to_string()),
                    });
                    stmts.push(Stmt::Continue);
                } else {
                    stmts.push(Stmt::Break);
                }
            }
            Terminator::Unreachable => {
                stmts.push(Stmt::Expr(self.expr_unreachable()));
            }
        }
        Ok(stmts)
    }

    fn rvalue_expr(
        &self,
        body: &TypedBody,
        rvalue: &Rvalue,
        closure_env: Option<&ClosureEnv>,
        expected_ty: Option<&MirType>,
    ) -> Result<Expr, TypedCodegenError> {
        match rvalue {
            Rvalue::Use(op) => self.operand_expr(body, op, closure_env, expected_ty),
            Rvalue::Discriminant(place) => self.discriminant_expr(body, place, closure_env),
            Rvalue::Ref(kind, place) => {
                let inner = self.place_expr(body, place, AccessKind::Copy, closure_env)?;
                let wrapper = match kind {
                    BorrowKind::Shared => "LrlRefShared::from_value",
                    BorrowKind::Mut => "LrlRefMut::from_value",
                };
                Ok(self.expr_call_path(wrapper, vec![inner]))
            }
        }
    }

    fn operand_expr(
        &self,
        body: &TypedBody,
        op: &Operand,
        closure_env: Option<&ClosureEnv>,
        expected_ty: Option<&MirType>,
    ) -> Result<Expr, TypedCodegenError> {
        match op {
            Operand::Copy(place) => self.place_expr(body, place, AccessKind::Copy, closure_env),
            Operand::Move(place) => self.place_expr(body, place, AccessKind::Move, closure_env),
            Operand::Constant(constant) => {
                self.constant_expr(body, constant, closure_env, expected_ty)
            }
        }
    }

    fn call_operand_expr(
        &self,
        body: &TypedBody,
        op: &CallOperand,
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Expr, TypedCodegenError> {
        match op {
            CallOperand::Operand(op) => self.operand_expr(body, op, closure_env, None),
            CallOperand::Borrow(_, place) => {
                self.place_expr(body, place, AccessKind::Copy, closure_env)
            }
        }
    }

    fn constant_expr(
        &self,
        body: &TypedBody,
        constant: &Constant,
        closure_env: Option<&ClosureEnv>,
        expected_ty: Option<&MirType>,
    ) -> Result<Expr, TypedCodegenError> {
        match &constant.literal {
            Literal::Unit => {
                if let Some(fn_ty) = expected_ty.filter(|ty| self.is_fn_type(ty)) {
                    self.erased_unit_callable_expr(fn_ty)
                } else {
                    Ok(self.expr_path("()"))
                }
            }
            Literal::Nat(n) => Ok(self.expr_lit_int(n.to_string())),
            Literal::Bool(b) => Ok(self.expr_lit_bool(*b)),
            Literal::GlobalDef(name) => {
                let safe = sanitize_name(name);
                Ok(self.expr_call(self.expr_path(safe), Vec::new()))
            }
            Literal::Recursor(ind_name) => self.recursor_expr(ind_name, expected_ty),
            Literal::OpaqueConst(reason) => {
                Ok(self.expr_call_path("LrlOpaque::new", vec![self.expr_lit_str(reason)]))
            }
            Literal::InductiveCtor(ctor, arity, _) => {
                let ctor_name = self
                    .ctor_name_map
                    .get(ctor)
                    .cloned()
                    .unwrap_or_else(|| "ctor".to_string());
                let _ = arity;
                Ok(self.expr_call(self.expr_path(ctor_name), Vec::new()))
            }
            Literal::Closure(idx, captures) => {
                let global_idx = body.closure_base + *idx;
                let fn_ty = expected_ty.unwrap_or(&constant.ty);
                let arg_ty = self.fn_arg_type(fn_ty).ok_or_else(|| {
                    TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedClosureType,
                        "unsupported closure type",
                    )
                })?;
                let ret_ty = self.fn_ret_type(fn_ty).ok_or_else(|| {
                    TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedClosureType,
                        "unsupported closure type",
                    )
                })?;
                let callable_ty = self.callable_dyn_type(arg_ty, ret_ty)?;
                let cap_expr = self.capture_tuple_expr(body, captures, closure_env)?;
                let adapter_expr = Expr::StructInit {
                    path: "LrlClosureAdapter".to_string(),
                    fields: vec![
                        ("cap".to_string(), cap_expr),
                        (
                            "func".to_string(),
                            self.expr_path(format!("closure_adapter_{}", global_idx)),
                        ),
                    ],
                };
                let rc_expr = self.expr_call_path("Rc::new", vec![adapter_expr]);
                Ok(Expr::Block(Block {
                    stmts: vec![Stmt::Let {
                        name: "__callable".to_string(),
                        mutable: false,
                        ty: Some(callable_ty),
                        value: Some(rc_expr),
                    }],
                    tail: Some(Box::new(self.expr_path("__callable"))),
                }))
            }
            Literal::Fix(idx, captures) => {
                let global_idx = body.closure_base + *idx;
                let fn_ty = expected_ty.unwrap_or(&constant.ty);
                let arg_ty = self.fn_arg_type(fn_ty).ok_or_else(|| {
                    TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedFixpointType,
                        "unsupported fixpoint type",
                    )
                })?;
                let ret_ty = self.fn_ret_type(fn_ty).ok_or_else(|| {
                    TypedCodegenError::unsupported(
                        TypedCodegenReason::UnsupportedFixpointType,
                        "unsupported fixpoint type",
                    )
                })?;
                let callable_ty = self.callable_dyn_type(arg_ty, ret_ty)?;
                let cap_expr = self.capture_tuple_expr(body, captures, closure_env)?;
                let cyclic_builder = Expr::Closure {
                    params: vec![Param {
                        name: "self_ref".to_string(),
                        ty: None,
                    }],
                    body: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(Expr::StructInit {
                            path: "LrlFixAdapter".to_string(),
                            fields: vec![
                                (
                                    "self_ref".to_string(),
                                    self.expr_method(self.expr_path("self_ref"), "clone", vec![]),
                                ),
                                ("cap".to_string(), self.expr_path("__caps")),
                                (
                                    "func".to_string(),
                                    self.expr_path(format!("fix_adapter_{}", global_idx)),
                                ),
                            ],
                        })),
                    },
                    is_move: true,
                };
                let rc_expr = self.expr_call_path("Rc::new_cyclic", vec![cyclic_builder]);
                Ok(Expr::Block(Block {
                    stmts: vec![
                        Stmt::Let {
                            name: "__caps".to_string(),
                            mutable: false,
                            ty: None,
                            value: Some(cap_expr),
                        },
                        Stmt::Let {
                            name: "__fix".to_string(),
                            mutable: false,
                            ty: None,
                            value: Some(rc_expr),
                        },
                        Stmt::Let {
                            name: "__callable".to_string(),
                            mutable: false,
                            ty: Some(callable_ty),
                            value: Some(self.expr_path("__fix")),
                        },
                    ],
                    tail: Some(Box::new(self.expr_path("__callable"))),
                }))
            }
        }
    }

    fn place_expr(
        &self,
        body: &TypedBody,
        place: &Place,
        access: AccessKind,
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Expr, TypedCodegenError> {
        if place.projection.is_empty() {
            return self.local_expr(body, place.local.index(), access);
        }

        if let Some(env) = closure_env {
            if place.local.index() == 1 && !place.projection.is_empty() {
                if let PlaceElem::Field(idx) = place.projection[0] {
                    if let Some(name) = env.capture_names.get(idx) {
                        // Captures are accessed inside the state-machine loop; clone to avoid
                        // moving values across iterations.
                        let capture_expr = self.expr_clone(self.expr_path(name.clone()));
                        if place.projection.len() == 1 {
                            return Ok(capture_expr);
                        }
                        let captures = self.closure_capture_types(&body.body)?;
                        let cap_ty = captures.get(idx).ok_or_else(|| {
                            TypedCodegenError::new("invalid closure capture index")
                        })?;
                        return self.project_from_expr(
                            body,
                            capture_expr,
                            cap_ty,
                            &place.projection[1..],
                        );
                    }
                }
            }
        }

        let base_expr = self.local_expr(body, place.local.index(), AccessKind::Copy)?;
        let base_ty = self
            .local_type(body, place.local.index())
            .ok_or_else(|| TypedCodegenError::new("missing local type"))?;
        self.project_from_expr(body, base_expr, base_ty, &place.projection)
    }

    fn project_from_expr(
        &self,
        body: &TypedBody,
        base_expr: Expr,
        base_ty: &MirType,
        projections: &[PlaceElem],
    ) -> Result<Expr, TypedCodegenError> {
        if projections.is_empty() {
            return Ok(base_expr);
        }

        let mut current_ty = base_ty.clone();
        let mut variant = None;
        let mut expr = base_expr;

        for proj in projections {
            match proj {
                PlaceElem::Downcast(idx) => {
                    variant = Some(*idx);
                }
                PlaceElem::Field(field_idx) => {
                    if matches!(current_ty, MirType::Nat) {
                        if variant == Some(1) && *field_idx == 0 {
                            current_ty = MirType::Nat;
                            expr = Expr::Binary {
                                op: BinaryOp::Sub,
                                left: Box::new(expr),
                                right: Box::new(self.expr_lit_int("1")),
                            };
                            variant = None;
                            continue;
                        }
                        return Err(TypedCodegenError::unsupported(
                            TypedCodegenReason::UnsupportedPlaceProjection,
                            "unsupported Nat projection in typed backend",
                        ));
                    }
                    let (adt_id, args) = match &current_ty {
                        MirType::Adt(adt_id, args) => (adt_id.clone(), args.clone()),
                        _ => {
                            return Err(TypedCodegenError::unsupported(
                                TypedCodegenReason::UnsupportedPlaceProjection,
                                "field projection only supported on ADTs",
                            ))
                        }
                    };
                    let layout = self
                        .adt_layouts
                        .get(&adt_id)
                        .ok_or_else(|| TypedCodegenError::new("missing ADT layout"))?;

                    current_ty = if let Some(next_ty) = self
                        .adt_layouts
                        .field_type(&adt_id, variant, *field_idx, &args)
                    {
                        next_ty
                    } else {
                        self.field_type_without_downcast(&adt_id, *field_idx, &args)
                            .ok_or_else(|| {
                                TypedCodegenError::unsupported(
                                    TypedCodegenReason::UnsupportedPlaceProjection,
                                    "unsupported field access",
                                )
                            })?
                    };

                    let adt_name = self.adt_name(&adt_id);

                    let extracted = if let Some(variant_idx) = variant.or_else(|| {
                        if layout.variants.len() == 1 {
                            Some(0)
                        } else {
                            None
                        }
                    }) {
                        let variant_layout = layout
                            .variants
                            .get(variant_idx)
                            .ok_or_else(|| TypedCodegenError::new("invalid variant"))?;
                        let ctor_name = self
                            .ctor_name_map
                            .get(&variant_layout.ctor)
                            .cloned()
                            .unwrap_or_else(|| format!("Ctor{}", variant_idx));
                        let mut pattern_parts = Vec::new();
                        for idx in 0..variant_layout.fields.len() {
                            if idx == *field_idx {
                                pattern_parts.push(Pat::Bind(format!("field_{}", idx)));
                            } else {
                                pattern_parts.push(Pat::Wild);
                            }
                        }
                        let pattern = if pattern_parts.is_empty() {
                            Pat::Path(format!("{}::{}", adt_name, ctor_name))
                        } else {
                            Pat::Tuple {
                                path: format!("{}::{}", adt_name, ctor_name),
                                args: pattern_parts,
                            }
                        };
                        let needs_unbox =
                            self.boxed_fields
                                .contains(&(adt_id.clone(), variant_idx, *field_idx));
                        let field_name = format!("field_{}", field_idx);
                        let field_expr = if needs_unbox {
                            self.expr_clone(Expr::Unary {
                                op: UnaryOp::Deref,
                                expr: Box::new(self.expr_path(field_name)),
                            })
                        } else {
                            self.expr_clone(self.expr_path(field_name))
                        };
                        Expr::Match {
                            scrutinee: Box::new(expr),
                            arms: vec![
                                MatchArm {
                                    pat: pattern,
                                    body: Block {
                                        stmts: Vec::new(),
                                        tail: Some(Box::new(field_expr)),
                                    },
                                },
                                MatchArm {
                                    pat: Pat::Wild,
                                    body: Block {
                                        stmts: Vec::new(),
                                        tail: Some(Box::new(self.expr_unreachable())),
                                    },
                                },
                            ],
                        }
                    } else {
                        let mut arms = Vec::new();
                        let mut has_arm = false;
                        for (variant_idx, variant_layout) in layout.variants.iter().enumerate() {
                            if *field_idx >= variant_layout.fields.len() {
                                continue;
                            }
                            let ctor_name = self
                                .ctor_name_map
                                .get(&variant_layout.ctor)
                                .cloned()
                                .unwrap_or_else(|| format!("Ctor{}", variant_idx));
                            let mut pattern_parts = Vec::new();
                            for idx in 0..variant_layout.fields.len() {
                                if idx == *field_idx {
                                    pattern_parts.push(Pat::Bind(format!("field_{}", idx)));
                                } else {
                                    pattern_parts.push(Pat::Wild);
                                }
                            }
                            let pattern = if pattern_parts.is_empty() {
                                Pat::Path(format!("{}::{}", adt_name, ctor_name))
                            } else {
                                Pat::Tuple {
                                    path: format!("{}::{}", adt_name, ctor_name),
                                    args: pattern_parts,
                                }
                            };
                            let needs_unbox = self.boxed_fields.contains(&(
                                adt_id.clone(),
                                variant_idx,
                                *field_idx,
                            ));
                            let field_name = format!("field_{}", field_idx);
                            let field_expr = if needs_unbox {
                                self.expr_clone(Expr::Unary {
                                    op: UnaryOp::Deref,
                                    expr: Box::new(self.expr_path(field_name)),
                                })
                            } else {
                                self.expr_clone(self.expr_path(field_name))
                            };
                            arms.push(MatchArm {
                                pat: pattern,
                                body: Block {
                                    stmts: Vec::new(),
                                    tail: Some(Box::new(field_expr)),
                                },
                            });
                            has_arm = true;
                        }
                        if !has_arm {
                            return Err(TypedCodegenError::unsupported(
                                TypedCodegenReason::UnsupportedPlaceProjection,
                                "missing downcast for multi-variant ADT",
                            ));
                        }
                        arms.push(MatchArm {
                            pat: Pat::Wild,
                            body: Block {
                                stmts: Vec::new(),
                                tail: Some(Box::new(self.expr_unreachable())),
                            },
                        });
                        Expr::Match {
                            scrutinee: Box::new(expr),
                            arms,
                        }
                    };

                    expr = extracted;
                    variant = None;
                }
                PlaceElem::Deref => {
                    match &current_ty {
                        MirType::Ref(_, inner, mutability) => {
                            expr = match mutability {
                                Mutability::Not | Mutability::Mut => {
                                    self.expr_method(expr, "read", vec![])
                                }
                            };
                            current_ty = (**inner).clone();
                        }
                        MirType::RawPtr(inner, mutability) => {
                            expr = match mutability {
                                Mutability::Not => {
                                    self.expr_call_path("runtime_raw_ptr_read", vec![expr])
                                }
                                Mutability::Mut => {
                                    self.expr_call_path("runtime_raw_ptr_read_mut", vec![expr])
                                }
                            };
                            current_ty = (**inner).clone();
                        }
                        _ => {
                            return Err(TypedCodegenError::unsupported(
                                TypedCodegenReason::UnsupportedPlaceProjection,
                                "deref projection on non-reference type",
                            ))
                        }
                    }
                    variant = None;
                }
                PlaceElem::Index(local) => {
                    let elem_ty =
                        self.index_item_type_for_container(&current_ty)
                            .ok_or_else(|| {
                                TypedCodegenError::unsupported(
                                    TypedCodegenReason::UnsupportedPlaceProjection,
                                    "index projection only supported on indexable containers",
                                )
                            })?;
                    let index_expr = self.local_expr(body, local.index(), AccessKind::Copy)?;
                    expr = self.expr_call_path("runtime_index", vec![expr, index_expr]);
                    current_ty = elem_ty;
                    variant = None;
                }
            }
        }

        Ok(expr)
    }

    fn discriminant_expr(
        &self,
        body: &TypedBody,
        place: &Place,
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Expr, TypedCodegenError> {
        let local_ty = self
            .local_type(body, place.local.index())
            .ok_or_else(|| TypedCodegenError::new("missing local type"))?;
        match local_ty {
            MirType::Bool => {
                let expr = self.place_expr(body, place, AccessKind::Copy, closure_env)?;
                Ok(Expr::If {
                    cond: Box::new(expr),
                    then_branch: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(self.expr_lit_int("0u64"))),
                    },
                    else_branch: Some(Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(self.expr_lit_int("1u64"))),
                    }),
                })
            }
            MirType::Nat => {
                let expr = self.place_expr(body, place, AccessKind::Copy, closure_env)?;
                Ok(Expr::If {
                    cond: Box::new(Expr::Binary {
                        op: BinaryOp::Eq,
                        left: Box::new(expr),
                        right: Box::new(self.expr_lit_int("0")),
                    }),
                    then_branch: Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(self.expr_lit_int("0u64"))),
                    },
                    else_branch: Some(Block {
                        stmts: Vec::new(),
                        tail: Some(Box::new(self.expr_lit_int("1u64"))),
                    }),
                })
            }
            MirType::Adt(adt_id, _args) => {
                let expr = self.place_expr(body, place, AccessKind::Copy, closure_env)?;
                let layout = self
                    .adt_layouts
                    .get(&adt_id)
                    .ok_or_else(|| TypedCodegenError::new("missing ADT layout"))?;
                let adt_name = self.adt_name(&adt_id);
                let mut arms = Vec::new();
                for (idx, variant) in layout.variants.iter().enumerate() {
                    let ctor_name = self
                        .ctor_name_map
                        .get(&variant.ctor)
                        .cloned()
                        .unwrap_or_else(|| format!("Ctor{}", idx));
                    let pattern = if variant.fields.is_empty() {
                        Pat::Path(format!("{}::{}", adt_name, ctor_name))
                    } else {
                        let fields = vec![Pat::Wild; variant.fields.len()];
                        Pat::Tuple {
                            path: format!("{}::{}", adt_name, ctor_name),
                            args: fields,
                        }
                    };
                    arms.push(MatchArm {
                        pat: pattern,
                        body: Block {
                            stmts: Vec::new(),
                            tail: Some(Box::new(self.expr_lit_int(format!("{}u64", idx)))),
                        },
                    });
                }
                // Generic ADTs may include a synthetic `__Phantom` variant in emitted Rust.
                // Treat it as unreachable for discriminant purposes.
                arms.push(MatchArm {
                    pat: Pat::Wild,
                    body: Block {
                        stmts: vec![Stmt::Expr(self.expr_unreachable())],
                        tail: None,
                    },
                });
                Ok(Expr::Match {
                    scrutinee: Box::new(expr),
                    arms,
                })
            }
            _ => Err(TypedCodegenError::new(
                "discriminant only supported for Bool, Nat, or ADT",
            )),
        }
    }

    fn local_expr(
        &self,
        body: &TypedBody,
        local_idx: usize,
        access: AccessKind,
    ) -> Result<Expr, TypedCodegenError> {
        let local_decl = body
            .body
            .local_decls
            .get(local_idx)
            .ok_or_else(|| TypedCodegenError::new("missing local type"))?;
        let move_is_non_consuming = local_decl.is_copy || self.is_fn_type(&local_decl.ty);
        let base = self.expr_path(format!("_{}", local_idx));
        match access {
            AccessKind::Copy => Ok(
                self.expr_clone(self.expr_expect(self.expr_as_ref(base), "uninitialized local"))
            ),
            AccessKind::Move if move_is_non_consuming => Ok(
                self.expr_clone(self.expr_expect(self.expr_as_ref(base), "uninitialized local"))
            ),
            AccessKind::Move => Ok(self.expr_expect(self.expr_take(base), "moved local")),
        }
    }

    fn rust_type(&self, ty: &MirType) -> Result<String, TypedCodegenError> {
        match ty {
            MirType::Unit => Ok("()".to_string()),
            MirType::Bool => Ok("bool".to_string()),
            MirType::Nat => Ok("u64".to_string()),
            MirType::IndexTerm(_) => Ok("usize".to_string()),
            MirType::Adt(adt_id, args) => {
                if self.prop_adts.contains(adt_id) {
                    return Ok("()".to_string());
                }
                let param_count = self.ids.adt_num_params(adt_id).unwrap_or(0);
                let mut rendered_args = Vec::new();
                for arg in args.iter().take(param_count) {
                    rendered_args.push(self.rust_type(arg)?);
                }
                if rendered_args.is_empty() {
                    Ok(self.adt_name(adt_id).to_string())
                } else {
                    Ok(format!(
                        "{}<{}>",
                        self.adt_name(adt_id),
                        rendered_args.join(", ")
                    ))
                }
            }
            MirType::Fn(kind, _regions, args, ret)
            | MirType::FnItem(_, kind, _regions, args, ret)
            | MirType::Closure(kind, _, _regions, args, ret) => {
                let _ = kind;
                let arg_ty = args
                    .get(0)
                    .ok_or_else(|| TypedCodegenError::new("missing function arg"))?;
                let arg_str = self.rust_type(arg_ty)?;
                let ret_str = self.rust_type(ret)?;
                Ok(format!("Rc<dyn LrlCallable<{}, {}>>", arg_str, ret_str))
            }
            MirType::Ref(_, inner, mutability) => {
                let inner = self.rust_type(inner)?;
                match mutability {
                    Mutability::Not => Ok(format!("LrlRefShared<{}>", inner)),
                    Mutability::Mut => Ok(format!("LrlRefMut<{}>", inner)),
                }
            }
            MirType::RawPtr(inner, mutability) => {
                let inner = self.rust_type(inner)?;
                match mutability {
                    Mutability::Not => Ok(format!("*const {}", inner)),
                    Mutability::Mut => Ok(format!("*mut {}", inner)),
                }
            }
            MirType::InteriorMutable(inner, kind) => {
                let inner = self.rust_type(inner)?;
                let wrapper = match kind {
                    IMKind::RefCell => "LrlRefCell",
                    IMKind::Mutex => "LrlMutex",
                    IMKind::Atomic => "LrlAtomic",
                };
                Ok(format!("{}<{}>", wrapper, inner))
            }
            MirType::Opaque { .. } => Ok("LrlOpaque".to_string()),
            MirType::Param(idx) => Ok(self.generic_param_name(*idx)),
        }
    }

    fn generic_param_name(&self, idx: usize) -> String {
        format!("T{}", idx)
    }

    fn interior_mutable_wrapper_for_adt(&self, adt_id: &AdtId) -> Option<&'static str> {
        match self.adt_name(adt_id) {
            "RefCell" => Some("LrlRefCell"),
            "Mutex" => Some("LrlMutex"),
            "Atomic" => Some("LrlAtomic"),
            _ => None,
        }
    }

    fn name_with_generics(&self, name: &str, generics: &[String]) -> String {
        if generics.is_empty() {
            name.to_string()
        } else {
            format!("{}<{}>", name, generics.join(", "))
        }
    }

    fn fn_name_with_generics(&self, name: &str, generics: &[String]) -> String {
        if generics.is_empty() {
            name.to_string()
        } else {
            let bounded = generics
                .iter()
                .map(|param| format!("{}: Clone + 'static", param))
                .collect::<Vec<_>>();
            format!("{}<{}>", name, bounded.join(", "))
        }
    }

    fn adt_generic_params(&self, adt_id: &AdtId) -> Vec<String> {
        (0..self.ids.adt_num_params(adt_id).unwrap_or(0))
            .map(|idx| self.generic_param_name(idx))
            .collect()
    }

    fn collect_param_indices_in_type(ty: &MirType, out: &mut BTreeSet<usize>) {
        match ty {
            MirType::Param(idx) => {
                out.insert(*idx);
            }
            MirType::Adt(_, args) => {
                for arg in args {
                    Self::collect_param_indices_in_type(arg, out);
                }
            }
            MirType::Ref(_, inner, _)
            | MirType::RawPtr(inner, _)
            | MirType::InteriorMutable(inner, _) => Self::collect_param_indices_in_type(inner, out),
            MirType::Fn(_, _, args, ret)
            | MirType::FnItem(_, _, _, args, ret)
            | MirType::Closure(_, _, _, args, ret) => {
                for arg in args {
                    Self::collect_param_indices_in_type(arg, out);
                }
                Self::collect_param_indices_in_type(ret, out);
            }
            MirType::Unit
            | MirType::Bool
            | MirType::Nat
            | MirType::IndexTerm(_)
            | MirType::Opaque { .. } => {}
        }
    }

    fn generics_for_types<'b, I>(&self, types: I) -> Vec<String>
    where
        I: IntoIterator<Item = &'b MirType>,
    {
        let mut indices = BTreeSet::new();
        for ty in types {
            Self::collect_param_indices_in_type(ty, &mut indices);
        }
        indices
            .into_iter()
            .map(|idx| self.generic_param_name(idx))
            .collect()
    }

    fn body_generics(&self, body: &TypedBody) -> Vec<String> {
        self.body_generic_indices(body)
            .into_iter()
            .map(|idx| self.generic_param_name(idx))
            .collect()
    }

    fn body_generic_indices(&self, body: &TypedBody) -> BTreeSet<usize> {
        let mut tys: Vec<&MirType> = Vec::new();
        if let Some(ret_ty) = body.body.local_decls.get(0).map(|decl| &decl.ty) {
            tys.push(ret_ty);
        }
        for idx in 1..=body.body.arg_count {
            if let Some(arg_ty) = body.body.local_decls.get(idx).map(|decl| &decl.ty) {
                tys.push(arg_ty);
            }
        }
        if self.is_closure_body(&body.body) {
            if let Some(env_decl) = body.body.local_decls.get(1) {
                for capture_ty in &env_decl.closure_captures {
                    tys.push(capture_ty);
                }
            }
        }
        let mut indices = BTreeSet::new();
        for ty in tys {
            Self::collect_param_indices_in_type(ty, &mut indices);
        }
        indices
    }

    fn option_local_type_annotation(
        &self,
        ty: &MirType,
        bound_generics: &BTreeSet<usize>,
    ) -> Result<Option<String>, TypedCodegenError> {
        let mut indices = BTreeSet::new();
        Self::collect_param_indices_in_type(ty, &mut indices);
        if indices.iter().any(|idx| !bound_generics.contains(idx)) {
            return Ok(None);
        }
        let local_ty = self.rust_type(ty)?;
        Ok(Some(format!("std::option::Option<{}>", local_ty)))
    }

    fn option_local_type_annotation_with_usage(
        &self,
        local_idx: usize,
        ty: &MirType,
        bound_generics: &BTreeSet<usize>,
        used_locals: &HashSet<usize>,
    ) -> Result<Option<String>, TypedCodegenError> {
        match self.option_local_type_annotation(ty, bound_generics)? {
            Some(ty) => Ok(Some(ty)),
            None if !used_locals.contains(&local_idx) => {
                Ok(Some("std::option::Option<()>".to_string()))
            }
            None => Ok(None),
        }
    }

    fn collect_used_local_indices(&self, body: &Body) -> HashSet<usize> {
        let mut used = HashSet::new();
        for block in &body.basic_blocks {
            for stmt in &block.statements {
                match stmt {
                    Statement::Assign(place, rv) => {
                        self.collect_place_local_indices(place, &mut used);
                        self.collect_rvalue_local_indices(rv, &mut used);
                    }
                    Statement::RuntimeCheck(check) => match check {
                        RuntimeCheckKind::RefCellBorrow { local }
                        | RuntimeCheckKind::MutexLock { local } => {
                            used.insert(local.index());
                        }
                        RuntimeCheckKind::BoundsCheck { local, index } => {
                            used.insert(local.index());
                            used.insert(index.index());
                        }
                    },
                    Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
                }
            }
            if let Some(term) = &block.terminator {
                self.collect_terminator_local_indices(term, &mut used);
            }
        }
        used
    }

    fn collect_terminator_local_indices(&self, term: &Terminator, used: &mut HashSet<usize>) {
        match term {
            Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => {}
            Terminator::SwitchInt { discr, .. } => self.collect_operand_local_indices(discr, used),
            Terminator::Call {
                func,
                args,
                destination,
                ..
            } => {
                self.collect_call_operand_local_indices(func, used);
                for arg in args {
                    self.collect_operand_local_indices(arg, used);
                }
                self.collect_place_local_indices(destination, used);
            }
        }
    }

    fn collect_rvalue_local_indices(&self, rv: &Rvalue, used: &mut HashSet<usize>) {
        match rv {
            Rvalue::Use(op) => self.collect_operand_local_indices(op, used),
            Rvalue::Ref(_, place) | Rvalue::Discriminant(place) => {
                self.collect_place_local_indices(place, used)
            }
        }
    }

    fn collect_call_operand_local_indices(&self, op: &CallOperand, used: &mut HashSet<usize>) {
        match op {
            CallOperand::Operand(operand) => self.collect_operand_local_indices(operand, used),
            CallOperand::Borrow(_, place) => self.collect_place_local_indices(place, used),
        }
    }

    fn collect_operand_local_indices(&self, op: &Operand, used: &mut HashSet<usize>) {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                self.collect_place_local_indices(place, used)
            }
            Operand::Constant(constant) => {
                if let Some(captures) = constant.literal.capture_operands() {
                    for capture in captures {
                        self.collect_operand_local_indices(capture, used);
                    }
                }
            }
        }
    }

    fn collect_place_local_indices(&self, place: &Place, used: &mut HashSet<usize>) {
        used.insert(place.local.index());
        for proj in &place.projection {
            if let PlaceElem::Index(local) = proj {
                used.insert(local.index());
            }
        }
    }

    fn rust_field_type(
        &self,
        adt_id: &AdtId,
        variant_idx: usize,
        field_idx: usize,
        field_ty: &MirType,
    ) -> Result<String, TypedCodegenError> {
        if self
            .boxed_fields
            .contains(&(adt_id.clone(), variant_idx, field_idx))
        {
            let inner = self.rust_type(field_ty)?;
            Ok(format!("Box<{}>", inner))
        } else {
            self.rust_type(field_ty)
        }
    }

    fn ctor_value_type(
        &self,
        adt_id: &AdtId,
        variant_idx: usize,
        arity: usize,
    ) -> Result<String, TypedCodegenError> {
        if adt_id.is_builtin(Builtin::Nat) {
            return if variant_idx == 0 {
                Ok("u64".to_string())
            } else {
                Ok("Rc<dyn LrlCallable<u64, u64>>".to_string())
            };
        }
        if adt_id.is_builtin(Builtin::Bool) {
            return Ok("bool".to_string());
        }
        if self.prop_adts.contains(adt_id) {
            if arity == 0 {
                return Ok("()".to_string());
            }
            let arg_types = self.ctor_runtime_arg_types(adt_id, variant_idx, arity)?;
            let mut ty = "()".to_string();
            for arg_ty in arg_types.iter().rev() {
                let arg_ty = self.rust_type(arg_ty)?;
                ty = format!("Rc<dyn LrlCallable<{}, {}>>", arg_ty, ty);
            }
            return Ok(ty);
        }
        if let Some(wrapper_name) = self.interior_mutable_wrapper_for_adt(adt_id) {
            let wrapper_ty =
                self.name_with_generics(wrapper_name, &self.adt_generic_params(adt_id));
            if arity == 0 {
                return Ok(wrapper_ty);
            }
            let arg_types = self.ctor_runtime_arg_types(adt_id, variant_idx, arity)?;
            let mut ty = wrapper_ty;
            for arg_ty in arg_types.iter().rev() {
                let arg_ty = self.rust_type(arg_ty)?;
                ty = format!("Rc<dyn LrlCallable<{}, {}>>", arg_ty, ty);
            }
            return Ok(ty);
        }
        let adt_name = self.adt_name(adt_id);
        let adt_ty = self.name_with_generics(adt_name, &self.adt_generic_params(adt_id));
        if arity == 0 {
            return Ok(adt_ty);
        }
        let arg_types = self.ctor_runtime_arg_types(adt_id, variant_idx, arity)?;
        let mut ty = adt_ty;
        for arg_ty in arg_types.iter().rev() {
            let arg_ty = self.rust_type(arg_ty)?;
            ty = format!("Rc<dyn LrlCallable<{}, {}>>", arg_ty, ty);
        }
        Ok(ty)
    }

    fn ctor_runtime_arg_types(
        &self,
        adt_id: &AdtId,
        variant_idx: usize,
        arity: usize,
    ) -> Result<Vec<MirType>, TypedCodegenError> {
        let layout = self
            .adt_layouts
            .get(adt_id)
            .ok_or_else(|| TypedCodegenError::new("missing ADT layout"))?;
        let variant = layout
            .variants
            .get(variant_idx)
            .ok_or_else(|| TypedCodegenError::new("invalid variant"))?;
        if arity < variant.fields.len() {
            return Err(TypedCodegenError::new(
                "constructor arity smaller than layout field count",
            ));
        }
        let erased_prefix = arity - variant.fields.len();
        let mut arg_types = Vec::with_capacity(arity);
        for _ in 0..erased_prefix {
            arg_types.push(MirType::Unit);
        }
        arg_types.extend(variant.fields.iter().cloned());
        Ok(arg_types)
    }

    fn ctor_value_expr(
        &self,
        adt_id: &AdtId,
        variant_idx: usize,
        arity: usize,
    ) -> Result<Expr, TypedCodegenError> {
        if adt_id.is_builtin(Builtin::Nat) {
            return if variant_idx == 0 {
                Ok(self.expr_lit_int("0u64"))
            } else {
                Ok(self.expr_call_path(
                    "Rc::new",
                    vec![Expr::Closure {
                        params: vec![Param {
                            name: "n".to_string(),
                            ty: Some("u64".to_string()),
                        }],
                        body: Block {
                            stmts: Vec::new(),
                            tail: Some(Box::new(Expr::Binary {
                                op: BinaryOp::Add,
                                left: Box::new(self.expr_path("n")),
                                right: Box::new(self.expr_lit_int("1")),
                            })),
                        },
                        is_move: false,
                    }],
                ))
            };
        }
        if adt_id.is_builtin(Builtin::Bool) {
            return if variant_idx == 0 {
                Ok(self.expr_lit_bool(true))
            } else {
                Ok(self.expr_lit_bool(false))
            };
        }
        if self.prop_adts.contains(adt_id) {
            if arity == 0 {
                return Ok(self.expr_path("()"));
            }
            let arg_types = self.ctor_runtime_arg_types(adt_id, variant_idx, arity)?;
            let mut arg_names = Vec::new();
            for i in 0..arity {
                arg_names.push(format!("a{}", i));
            }
            let arg_type_names: Vec<String> = arg_types
                .iter()
                .map(|ty| self.rust_type(ty))
                .collect::<Result<_, _>>()?;
            let final_expr = self.expr_path("()");
            return Ok(self.curried_entry_expr(
                &arg_names,
                &arg_type_names,
                &[],
                &final_expr,
                "()",
            ));
        }

        let adt_name = self.adt_name(adt_id);
        let adt_ty = self.name_with_generics(adt_name, &self.adt_generic_params(adt_id));
        let layout = self
            .adt_layouts
            .get(adt_id)
            .ok_or_else(|| TypedCodegenError::new("missing ADT layout"))?;
        let variant = layout
            .variants
            .get(variant_idx)
            .ok_or_else(|| TypedCodegenError::new("invalid variant"))?;
        let ctor_name = self
            .ctor_name_map
            .get(&variant.ctor)
            .cloned()
            .unwrap_or_else(|| format!("Ctor{}", variant_idx));

        if let Some(wrapper_name) = self.interior_mutable_wrapper_for_adt(adt_id) {
            if variant.fields.len() != 1 {
                return Err(TypedCodegenError::new(
                    "interior mutable constructor must have exactly one payload field",
                ));
            }
            if arity == 0 {
                return Err(TypedCodegenError::new(
                    "interior mutable constructor missing payload",
                ));
            }
            let wrapper_ty =
                self.name_with_generics(wrapper_name, &self.adt_generic_params(adt_id));
            let arg_types = self.ctor_runtime_arg_types(adt_id, variant_idx, arity)?;
            let mut arg_names = Vec::new();
            for i in 0..arity {
                arg_names.push(format!("a{}", i));
            }
            let arg_type_names: Vec<String> = arg_types
                .iter()
                .map(|ty| self.rust_type(ty))
                .collect::<Result<_, _>>()?;
            let value_arg_name = format!("a{}", arity - variant.fields.len());
            let final_expr = Expr::StructInit {
                // Use the nominal wrapper path here; generic arguments are inferred from context.
                path: wrapper_name.to_string(),
                fields: vec![("value".to_string(), self.expr_path(value_arg_name))],
            };
            return Ok(self.curried_entry_expr(
                &arg_names,
                &arg_type_names,
                &[],
                &final_expr,
                &wrapper_ty,
            ));
        }

        if arity == 0 {
            return Ok(self.expr_path(format!("{}::{}", adt_name, ctor_name)));
        }

        let arg_types = self.ctor_runtime_arg_types(adt_id, variant_idx, arity)?;
        let mut arg_names = Vec::new();
        for i in 0..arity {
            arg_names.push(format!("a{}", i));
        }
        let arg_type_names: Vec<String> = arg_types
            .iter()
            .map(|ty| self.rust_type(ty))
            .collect::<Result<_, _>>()?;

        let mut ctor_args = Vec::new();
        let first_field_arg_idx = arity - variant.fields.len();
        for field_idx in 0..variant.fields.len() {
            let arg_name = format!("a{}", first_field_arg_idx + field_idx);
            if self
                .boxed_fields
                .contains(&(adt_id.clone(), variant_idx, field_idx))
            {
                ctor_args.push(self.expr_call_path("Box::new", vec![self.expr_path(arg_name)]));
            } else {
                ctor_args.push(self.expr_path(arg_name));
            }
        }
        let ctor_expr = self.expr_path(format!("{}::{}", adt_name, ctor_name));
        let final_expr = if ctor_args.is_empty() {
            ctor_expr
        } else {
            self.expr_call(ctor_expr, ctor_args)
        };
        Ok(self.curried_entry_expr(&arg_names, &arg_type_names, &[], &final_expr, &adt_ty))
    }

    fn fn_arg_type<'b>(&self, ty: &'b MirType) -> Option<&'b MirType> {
        match ty {
            MirType::Fn(_, _, args, _) => args.get(0),
            MirType::FnItem(_, _, _, args, _) => args.get(0),
            MirType::Closure(_, _, _, args, _) => args.get(0),
            _ => None,
        }
    }

    fn fn_ret_type<'b>(&self, ty: &'b MirType) -> Option<&'b MirType> {
        match ty {
            MirType::Fn(_, _, _, ret) => Some(ret),
            MirType::FnItem(_, _, _, _, ret) => Some(ret),
            MirType::Closure(_, _, _, _, ret) => Some(ret),
            _ => None,
        }
    }

    fn erased_unit_callable_expr(&self, fn_ty: &MirType) -> Result<Expr, TypedCodegenError> {
        let arg_ty = self.fn_arg_type(fn_ty).ok_or_else(|| {
            TypedCodegenError::unsupported(
                TypedCodegenReason::UnsupportedClosureType,
                "function-typed unit literal is missing argument type",
            )
        })?;
        let ret_ty = self.fn_ret_type(fn_ty).ok_or_else(|| {
            TypedCodegenError::unsupported(
                TypedCodegenReason::UnsupportedClosureType,
                "function-typed unit literal is missing return type",
            )
        })?;
        let callable_ty = self.callable_dyn_type(arg_ty, ret_ty)?;
        let arg_ty_str = self.rust_type(arg_ty)?;
        let panic_expr = Expr::MacroCall {
            name: "panic".to_string(),
            args: vec![self
                .expr_lit_str("attempted to execute erased function literal (unit placeholder)")],
        };
        let closure = Expr::Closure {
            params: vec![Param {
                name: "__erased_arg".to_string(),
                ty: Some(arg_ty_str),
            }],
            body: Block {
                stmts: vec![Stmt::Expr(panic_expr)],
                tail: None,
            },
            is_move: true,
        };
        let rc_expr = self.expr_call_path("Rc::new", vec![closure]);
        Ok(Expr::Block(Block {
            stmts: vec![Stmt::Let {
                name: "__callable".to_string(),
                mutable: false,
                ty: Some(callable_ty),
                value: Some(rc_expr),
            }],
            tail: Some(Box::new(self.expr_path("__callable"))),
        }))
    }

    fn closure_capture_types(&self, body: &Body) -> Result<Vec<MirType>, TypedCodegenError> {
        let env_decl = body
            .local_decls
            .get(1)
            .ok_or_else(|| TypedCodegenError::new("missing env local"))?;
        Ok(env_decl.closure_captures.clone())
    }

    fn field_type(
        &self,
        ty: &MirType,
        variant: Option<usize>,
        field_idx: usize,
    ) -> Option<MirType> {
        match ty {
            MirType::Adt(adt_id, args) => self
                .adt_layouts
                .field_type(adt_id, variant, field_idx, args),
            _ => None,
        }
    }

    fn field_type_without_downcast(
        &self,
        adt_id: &AdtId,
        field_idx: usize,
        args: &[MirType],
    ) -> Option<MirType> {
        let layout = self.adt_layouts.get(adt_id)?;
        let mut field_ty: Option<MirType> = None;
        for variant in &layout.variants {
            if let Some(ty_template) = variant.fields.get(field_idx) {
                let ty = ty_template.substitute_params(args);
                if let Some(existing) = &field_ty {
                    if existing != &ty {
                        return None;
                    }
                } else {
                    field_ty = Some(ty);
                }
            }
        }
        field_ty
    }

    fn place_type(&self, body: &TypedBody, place: &Place) -> Option<MirType> {
        if self.is_closure_body(&body.body) && place.local.index() == 1 {
            if !place.projection.is_empty() {
                if let PlaceElem::Field(idx) = place.projection[0] {
                    let captures = self.closure_capture_types(&body.body).ok()?;
                    let mut current_ty = captures.get(idx).cloned()?;
                    let mut variant = None;
                    for proj in place.projection.iter().skip(1) {
                        match proj {
                            PlaceElem::Downcast(idx) => variant = Some(*idx),
                            PlaceElem::Field(field_idx) => {
                                current_ty = self.field_type(&current_ty, variant, *field_idx)?;
                                variant = None;
                            }
                            PlaceElem::Deref => {
                                current_ty = match current_ty {
                                    MirType::Ref(_, inner, _) | MirType::RawPtr(inner, _) => *inner,
                                    _ => return None,
                                };
                                variant = None;
                            }
                            PlaceElem::Index(_) => {
                                current_ty = self.index_item_type_for_container(&current_ty)?;
                                variant = None;
                            }
                        }
                    }
                    return Some(current_ty);
                }
            }
            return None;
        }

        let mut current_ty = self.local_type(body, place.local.index())?.clone();
        let mut variant = None;
        for proj in &place.projection {
            match proj {
                PlaceElem::Downcast(idx) => variant = Some(*idx),
                PlaceElem::Field(field_idx) => {
                    current_ty = self.field_type(&current_ty, variant, *field_idx)?;
                    variant = None;
                }
                PlaceElem::Deref => {
                    current_ty = match current_ty {
                        MirType::Ref(_, inner, _) | MirType::RawPtr(inner, _) => *inner,
                        _ => return None,
                    };
                    variant = None;
                }
                PlaceElem::Index(_) => {
                    current_ty = self.index_item_type_for_container(&current_ty)?;
                    variant = None;
                }
            }
        }
        Some(current_ty)
    }

    fn local_type<'b>(&self, body: &'b TypedBody, idx: usize) -> Option<&'b MirType> {
        body.body.local_decls.get(idx).map(|decl| &decl.ty)
    }

    fn index_item_type_for_container(&self, ty: &MirType) -> Option<MirType> {
        match ty {
            MirType::Adt(adt_id, args) => self.index_item_type_for_adt(adt_id, args),
            _ => None,
        }
    }

    fn index_item_type_for_adt(&self, adt_id: &AdtId, args: &[MirType]) -> Option<MirType> {
        let list_builtin = self.ids.builtin_adt(Builtin::List);
        if list_builtin.as_ref().is_some_and(|id| id == adt_id) {
            return args.first().cloned();
        }
        if !self.ids.is_indexable_adt(adt_id) {
            return None;
        }
        let item_ty = if let Some(first) = args.first() {
            first.clone()
        } else {
            self.infer_monomorphic_index_item_type(adt_id)?
        };
        Some(item_ty)
    }

    fn infer_monomorphic_index_item_type(&self, adt_id: &AdtId) -> Option<MirType> {
        let layout = self.adt_layouts.get(adt_id)?;
        let mut candidate: Option<MirType> = None;
        for variant in &layout.variants {
            for field_ty in &variant.fields {
                let mut field_candidate = self.index_item_type_from_field_shallow(field_ty);
                if field_candidate.is_none() && variant.fields.len() == 1 {
                    field_candidate = Some(field_ty.clone());
                }
                if let Some(item_ty) = field_candidate {
                    if let Some(existing) = &candidate {
                        if existing != &item_ty {
                            return None;
                        }
                    } else {
                        candidate = Some(item_ty);
                    }
                }
            }
        }
        candidate
    }

    fn index_item_type_from_field_shallow(&self, field_ty: &MirType) -> Option<MirType> {
        let MirType::Adt(field_adt, field_args) = field_ty else {
            return None;
        };
        let list_builtin = self.ids.builtin_adt(Builtin::List);
        if list_builtin.as_ref().is_some_and(|id| id == field_adt) {
            return field_args.first().cloned();
        }
        if self.ids.is_indexable_adt(field_adt) {
            return field_args.first().cloned();
        }
        None
    }

    fn select_index_source_field(
        &self,
        fields: &[MirType],
        item_ty: &MirType,
    ) -> Option<(usize, IndexSourceKind)> {
        for (idx, field_ty) in fields.iter().enumerate() {
            if field_ty == item_ty {
                return Some((idx, IndexSourceKind::Direct));
            }
        }
        for (idx, field_ty) in fields.iter().enumerate() {
            if let Some(field_item_ty) = self.index_item_type_from_field_shallow(field_ty) {
                if &field_item_ty == item_ty {
                    return Some((idx, IndexSourceKind::Nested));
                }
            }
        }
        None
    }

    fn capture_tuple_type(&self, captures: &[MirType]) -> Result<String, TypedCodegenError> {
        if captures.is_empty() {
            return Ok("()".to_string());
        }
        let parts = captures
            .iter()
            .map(|ty| self.rust_type(ty))
            .collect::<Result<Vec<_>, _>>()?;
        if parts.len() == 1 {
            Ok(format!("({},)", parts[0]))
        } else {
            Ok(format!("({})", parts.join(", ")))
        }
    }

    fn capture_tuple_expr(
        &self,
        body: &TypedBody,
        captures: &[Operand],
        closure_env: Option<&ClosureEnv>,
    ) -> Result<Expr, TypedCodegenError> {
        if captures.is_empty() {
            return Ok(self.expr_path("()"));
        }
        let elems = captures
            .iter()
            .map(|op| self.operand_expr(body, op, closure_env, None))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Expr::Tuple(elems))
    }

    fn callable_dyn_type(
        &self,
        arg_ty: &MirType,
        ret_ty: &MirType,
    ) -> Result<String, TypedCodegenError> {
        Ok(format!(
            "Rc<dyn LrlCallable<{}, {}>>",
            self.rust_type(arg_ty)?,
            self.rust_type(ret_ty)?
        ))
    }

    fn callable_literal_expr(
        &self,
        arg_ty: &MirType,
        ret_ty: &MirType,
        closure: Expr,
    ) -> Result<Expr, TypedCodegenError> {
        let callable_ty = self.callable_dyn_type(arg_ty, ret_ty)?;
        let rc_expr = self.expr_call_path("Rc::new", vec![closure]);
        Ok(Expr::Block(Block {
            stmts: vec![Stmt::Let {
                name: "__callable".to_string(),
                mutable: false,
                ty: Some(callable_ty),
                value: Some(rc_expr),
            }],
            tail: Some(Box::new(self.expr_path("__callable"))),
        }))
    }

    fn is_fn_type(&self, ty: &MirType) -> bool {
        matches!(
            ty,
            MirType::Fn(_, _, _, _)
                | MirType::FnItem(_, _, _, _, _)
                | MirType::Closure(_, _, _, _, _)
        )
    }

    fn is_closure_body(&self, body: &Body) -> bool {
        body.arg_count == 2 && body.local_decls.len() >= 3
    }

    fn adt_name(&self, adt_id: &AdtId) -> &str {
        self.adt_name_map
            .get(adt_id)
            .map(|s| s.as_str())
            .unwrap_or("UnknownAdt")
    }

    fn closure_body_index(&self, body: &TypedBody) -> usize {
        body.name
            .strip_prefix("closure_")
            .and_then(|idx| idx.parse::<usize>().ok())
            .unwrap_or(body.closure_base)
    }

    fn is_direct_recursive(&self, field_ty: &MirType, adt_id: &AdtId) -> bool {
        matches!(field_ty, MirType::Adt(id, _) if id == adt_id)
    }

    fn expr_path(&self, name: impl Into<String>) -> Expr {
        Expr::Path(name.into())
    }

    fn expr_lit_int(&self, value: impl Into<String>) -> Expr {
        Expr::Lit(Lit::Int(value.into()))
    }

    fn expr_lit_bool(&self, value: bool) -> Expr {
        Expr::Lit(Lit::Bool(value))
    }

    fn expr_lit_str(&self, value: impl Into<String>) -> Expr {
        Expr::Lit(Lit::Str(value.into()))
    }

    fn expr_call(&self, func: Expr, args: Vec<Expr>) -> Expr {
        Expr::Call {
            func: Box::new(func),
            args,
        }
    }

    fn expr_call_callable(&self, callable: Expr, arg: Expr) -> Expr {
        self.expr_method(callable, "call", vec![arg])
    }

    fn expr_call_path(&self, path: &str, args: Vec<Expr>) -> Expr {
        self.expr_call(self.expr_path(path), args)
    }

    fn expr_method(&self, receiver: Expr, method: &str, args: Vec<Expr>) -> Expr {
        Expr::MethodCall {
            receiver: Box::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn expr_clone(&self, expr: Expr) -> Expr {
        self.expr_method(expr, "clone", vec![])
    }

    fn expr_as_ref(&self, expr: Expr) -> Expr {
        self.expr_method(expr, "as_ref", vec![])
    }

    fn expr_take(&self, expr: Expr) -> Expr {
        self.expr_method(expr, "take", vec![])
    }

    fn expr_expect(&self, expr: Expr, msg: &str) -> Expr {
        self.expr_method(expr, "expect", vec![self.expr_lit_str(msg)])
    }

    fn expr_some(&self, expr: Expr) -> Expr {
        self.expr_call_path("std::option::Option::Some", vec![expr])
    }

    fn expr_none(&self) -> Expr {
        self.expr_path("std::option::Option::None")
    }

    fn expr_unreachable(&self) -> Expr {
        Expr::MacroCall {
            name: "unreachable".to_string(),
            args: Vec::new(),
        }
    }
}

struct RustWriter {
    out: String,
    indent: usize,
}

impl RustWriter {
    fn new() -> Self {
        Self {
            out: String::new(),
            indent: 0,
        }
    }

    fn line(&mut self, text: &str) {
        for _ in 0..self.indent {
            self.out.push_str("    ");
        }
        self.out.push_str(text);
        self.out.push('\n');
    }

    fn blank(&mut self) {
        self.out.push('\n');
    }

    fn indent<F, E>(&mut self, f: F) -> Result<(), E>
    where
        F: FnOnce(&mut Self) -> Result<(), E>,
    {
        self.indent += 1;
        let result = f(self);
        self.indent -= 1;
        result
    }

    fn finish(self) -> String {
        self.out
    }
}

type RustType = String;

#[allow(dead_code)]
#[derive(Debug, Clone)]
enum Item {
    CrateAttr(String),
    Use(String),
    Raw(String),
    Enum {
        name: String,
        derives: Vec<String>,
        variants: Vec<EnumVariant>,
    },
    Struct {
        name: String,
        derives: Vec<String>,
        fields: Vec<StructField>,
    },
    TypeAlias {
        name: String,
        ty: RustType,
    },
    Fn {
        name: String,
        params: Vec<Param>,
        ret: Option<RustType>,
        body: Block,
    },
    Impl {
        target: String,
        items: Vec<ImplItem>,
    },
}

#[derive(Debug, Clone)]
struct EnumVariant {
    name: String,
    fields: Vec<RustType>,
}

#[derive(Debug, Clone)]
struct StructField {
    name: String,
    ty: RustType,
}

#[derive(Debug, Clone)]
struct Param {
    name: String,
    ty: Option<RustType>,
}

#[derive(Debug, Clone)]
struct Block {
    stmts: Vec<Stmt>,
    tail: Option<Box<Expr>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
enum Stmt {
    Let {
        name: String,
        mutable: bool,
        ty: Option<RustType>,
        value: Option<Expr>,
    },
    Assign {
        target: Expr,
        value: Expr,
    },
    Expr(Expr),
    Return(Option<Expr>),
    Break,
    Continue,
    Loop(Block),
}

#[derive(Debug, Clone)]
enum Expr {
    Path(String),
    Tuple(Vec<Expr>),
    StructInit {
        path: String,
        fields: Vec<(String, Expr)>,
    },
    Lit(Lit),
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Expr>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Block(Block),
    If {
        cond: Box<Expr>,
        then_branch: Block,
        else_branch: Option<Block>,
    },
    Closure {
        params: Vec<Param>,
        body: Block,
        is_move: bool,
    },
    Ref {
        mutable: bool,
        expr: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Cast {
        expr: Box<Expr>,
        ty: RustType,
    },
    MacroCall {
        name: String,
        args: Vec<Expr>,
    },
}

#[derive(Debug, Clone)]
enum Lit {
    Bool(bool),
    Int(String),
    Str(String),
}

#[derive(Debug, Clone)]
struct MatchArm {
    pat: Pat,
    body: Block,
}

#[derive(Debug, Clone)]
enum Pat {
    Wild,
    Lit(Lit),
    Path(String),
    Bind(String),
    Tuple { path: String, args: Vec<Pat> },
}

#[derive(Debug, Clone, Copy)]
enum UnaryOp {
    Deref,
}

#[derive(Debug, Clone, Copy)]
enum BinaryOp {
    Add,
    Sub,
    Eq,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
enum ImplItem {
    Fn {
        name: String,
        params: Vec<Param>,
        ret: Option<RustType>,
        body: Block,
    },
}

fn render_items(items: &[Item]) -> String {
    let mut writer = RustWriter::new();
    for (idx, item) in items.iter().enumerate() {
        write_item(&mut writer, item);
        if idx + 1 < items.len() {
            writer.blank();
        }
    }
    writer.finish()
}

fn write_item(writer: &mut RustWriter, item: &Item) {
    match item {
        Item::CrateAttr(attr) => writer.line(&format!("#![{}]", attr)),
        Item::Use(path) => writer.line(&format!("use {};", path)),
        Item::Raw(text) => {
            for line in text.lines() {
                if line.is_empty() {
                    writer.blank();
                } else {
                    writer.line(line);
                }
            }
        }
        Item::Enum {
            name,
            derives,
            variants,
        } => {
            if !derives.is_empty() {
                writer.line(&format!("#[derive({})]", derives.join(", ")));
            }
            writer.line(&format!("enum {} {{", name));
            let _ = writer.indent(|writer| {
                for variant in variants {
                    if variant.fields.is_empty() {
                        writer.line(&format!("{},", variant.name));
                    } else {
                        writer.line(&format!("{}({}),", variant.name, variant.fields.join(", ")));
                    }
                }
                Ok::<(), ()>(())
            });
            writer.line("}");
        }
        Item::Struct {
            name,
            derives,
            fields,
        } => {
            if !derives.is_empty() {
                writer.line(&format!("#[derive({})]", derives.join(", ")));
            }
            writer.line(&format!("struct {} {{", name));
            let _ = writer.indent(|writer| {
                for field in fields {
                    writer.line(&format!("{}: {},", field.name, field.ty));
                }
                Ok::<(), ()>(())
            });
            writer.line("}");
        }
        Item::TypeAlias { name, ty } => {
            writer.line(&format!("type {} = {};", name, ty));
        }
        Item::Fn {
            name,
            params,
            ret,
            body,
        } => {
            let params_str = params
                .iter()
                .map(|p| match &p.ty {
                    Some(ty) => format!("{}: {}", p.name, ty),
                    None => p.name.clone(),
                })
                .collect::<Vec<_>>()
                .join(", ");
            if let Some(ret) = ret {
                writer.line(&format!("fn {}({}) -> {} {{", name, params_str, ret));
            } else {
                writer.line(&format!("fn {}({}) {{", name, params_str));
            }
            let _ = writer.indent(|writer| {
                write_block_body(writer, body);
                Ok::<(), ()>(())
            });
            writer.line("}");
        }
        Item::Impl { target, items } => {
            writer.line(&format!("impl {} {{", target));
            let _ = writer.indent(|writer| {
                for (idx, item) in items.iter().enumerate() {
                    if idx > 0 {
                        writer.blank();
                    }
                    match item {
                        ImplItem::Fn {
                            name,
                            params,
                            ret,
                            body,
                        } => {
                            let params_str = params
                                .iter()
                                .map(|p| match &p.ty {
                                    Some(ty) => format!("{}: {}", p.name, ty),
                                    None => p.name.clone(),
                                })
                                .collect::<Vec<_>>()
                                .join(", ");
                            if let Some(ret) = ret {
                                writer.line(&format!("fn {}({}) -> {} {{", name, params_str, ret));
                            } else {
                                writer.line(&format!("fn {}({}) {{", name, params_str));
                            }
                            let _ = writer.indent(|writer| {
                                write_block_body(writer, body);
                                Ok::<(), ()>(())
                            });
                            writer.line("}");
                        }
                    }
                }
                Ok::<(), ()>(())
            });
            writer.line("}");
        }
    }
}

fn write_block_body(writer: &mut RustWriter, block: &Block) {
    for stmt in &block.stmts {
        write_stmt(writer, stmt);
    }
    if let Some(expr) = &block.tail {
        writer.line(&expr_to_string(expr));
    }
}

fn write_stmt(writer: &mut RustWriter, stmt: &Stmt) {
    match stmt {
        Stmt::Let {
            name,
            mutable,
            ty,
            value,
        } => {
            let mut line = String::new();
            if *mutable {
                line.push_str("let mut ");
            } else {
                line.push_str("let ");
            }
            line.push_str(name);
            if let Some(ty) = ty {
                line.push_str(": ");
                line.push_str(ty);
            }
            if let Some(value) = value {
                line.push_str(" = ");
                line.push_str(&expr_to_string(value));
            }
            line.push(';');
            writer.line(&line);
        }
        Stmt::Assign { target, value } => {
            writer.line(&format!(
                "{} = {};",
                expr_to_string(target),
                expr_to_string(value)
            ));
        }
        Stmt::Expr(expr) => {
            writer.line(&format!("{};", expr_to_string(expr)));
        }
        Stmt::Return(expr) => {
            if let Some(expr) = expr {
                writer.line(&format!("return {};", expr_to_string(expr)));
            } else {
                writer.line("return;");
            }
        }
        Stmt::Break => writer.line("break;"),
        Stmt::Continue => writer.line("continue;"),
        Stmt::Loop(block) => {
            writer.line("loop {");
            let _ = writer.indent(|writer| {
                write_block_body(writer, block);
                Ok::<(), ()>(())
            });
            writer.line("}");
        }
    }
}

fn expr_to_string(expr: &Expr) -> String {
    expr_to_string_prec(expr, 0)
}

fn expr_to_string_prec(expr: &Expr, prec: u8) -> String {
    let (expr_prec, rendered) = match expr {
        Expr::Path(name) => (5, name.clone()),
        Expr::Tuple(items) => {
            if items.is_empty() {
                (5, "()".to_string())
            } else if items.len() == 1 {
                (5, format!("({},)", expr_to_string(&items[0])))
            } else {
                (
                    5,
                    format!(
                        "({})",
                        items
                            .iter()
                            .map(expr_to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                )
            }
        }
        Expr::StructInit { path, fields } => {
            let fields_str = fields
                .iter()
                .map(|(name, value)| format!("{}: {}", name, expr_to_string(value)))
                .collect::<Vec<_>>()
                .join(", ");
            (5, format!("{} {{ {} }}", path, fields_str))
        }
        Expr::Lit(lit) => (5, lit_to_string(lit)),
        Expr::Call { func, args } => {
            let func_str = wrap_if_needed(func, 4);
            let args_str = args
                .iter()
                .map(expr_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            (4, format!("{}({})", func_str, args_str))
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let recv_str = wrap_if_needed(receiver, 4);
            let args_str = args
                .iter()
                .map(expr_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            (4, format!("{}.{}({})", recv_str, method, args_str))
        }
        Expr::Match { scrutinee, arms } => {
            let mut out = String::new();
            out.push_str("match ");
            out.push_str(&expr_to_string(scrutinee));
            out.push_str(" {");
            for arm in arms {
                out.push(' ');
                out.push_str(&pat_to_string(&arm.pat));
                out.push_str(" => ");
                out.push_str(&block_to_string(&arm.body));
                out.push(',');
            }
            out.push_str(" }");
            (0, out)
        }
        Expr::Block(block) => (0, block_to_string(block)),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let mut out = String::new();
            out.push_str("if ");
            out.push_str(&expr_to_string(cond));
            out.push(' ');
            out.push_str(&block_to_string(then_branch));
            if let Some(else_branch) = else_branch {
                out.push_str(" else ");
                out.push_str(&block_to_string(else_branch));
            }
            (0, out)
        }
        Expr::Closure {
            params,
            body,
            is_move,
        } => {
            let mut out = String::new();
            if *is_move {
                out.push_str("move ");
            }
            out.push('|');
            out.push_str(
                &params
                    .iter()
                    .map(|p| match &p.ty {
                        Some(ty) => format!("{}: {}", p.name, ty),
                        None => p.name.clone(),
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            out.push_str("| ");
            out.push_str(&block_to_string(body));
            (0, out)
        }
        Expr::Ref { mutable, expr } => {
            let inner = wrap_if_needed(expr, 3);
            if *mutable {
                (3, format!("&mut {}", inner))
            } else {
                (3, format!("&{}", inner))
            }
        }
        Expr::Unary { op, expr } => {
            let inner = wrap_if_needed(expr, 3);
            let op_str = match op {
                UnaryOp::Deref => "*",
            };
            (3, format!("{}{}", op_str, inner))
        }
        Expr::Binary { op, left, right } => {
            let left_str = wrap_if_needed(left, 2);
            let right_str = wrap_if_needed(right, 2);
            let op_str = match op {
                BinaryOp::Add => "+",
                BinaryOp::Sub => "-",
                BinaryOp::Eq => "==",
            };
            (2, format!("{} {} {}", left_str, op_str, right_str))
        }
        Expr::Cast { expr, ty } => {
            let inner = wrap_if_needed(expr, 1);
            (1, format!("{} as {}", inner, ty))
        }
        Expr::MacroCall { name, args } => {
            let args_str = args
                .iter()
                .map(expr_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            (5, format!("{}!({})", name, args_str))
        }
    };

    if expr_prec < prec {
        format!("({})", rendered)
    } else {
        rendered
    }
}

fn wrap_if_needed(expr: &Expr, prec: u8) -> String {
    expr_to_string_prec(expr, prec)
}

fn block_to_string(block: &Block) -> String {
    let mut out = String::new();
    out.push('{');
    let mut first = true;
    for stmt in &block.stmts {
        if first {
            out.push(' ');
            first = false;
        } else {
            out.push(' ');
        }
        out.push_str(&stmt_to_inline(stmt));
    }
    if let Some(expr) = &block.tail {
        if first {
            out.push(' ');
        } else {
            out.push(' ');
        }
        out.push_str(&expr_to_string(expr));
    }
    out.push(' ');
    out.push('}');
    out
}

fn stmt_to_inline(stmt: &Stmt) -> String {
    match stmt {
        Stmt::Let {
            name,
            mutable,
            ty,
            value,
        } => {
            let mut out = String::new();
            if *mutable {
                out.push_str("let mut ");
            } else {
                out.push_str("let ");
            }
            out.push_str(name);
            if let Some(ty) = ty {
                out.push_str(": ");
                out.push_str(ty);
            }
            if let Some(value) = value {
                out.push_str(" = ");
                out.push_str(&expr_to_string(value));
            }
            out.push(';');
            out
        }
        Stmt::Assign { target, value } => {
            format!("{} = {};", expr_to_string(target), expr_to_string(value))
        }
        Stmt::Expr(expr) => format!("{};", expr_to_string(expr)),
        Stmt::Return(expr) => {
            if let Some(expr) = expr {
                format!("return {};", expr_to_string(expr))
            } else {
                "return;".to_string()
            }
        }
        Stmt::Break => "break;".to_string(),
        Stmt::Continue => "continue;".to_string(),
        Stmt::Loop(block) => format!("loop {}", block_to_string(block)),
    }
}

fn pat_to_string(pat: &Pat) -> String {
    match pat {
        Pat::Wild => "_".to_string(),
        Pat::Lit(lit) => lit_to_string(lit),
        Pat::Path(path) => path.clone(),
        Pat::Bind(name) => name.clone(),
        Pat::Tuple { path, args } => {
            if args.is_empty() {
                path.clone()
            } else {
                format!(
                    "{}({})",
                    path,
                    args.iter()
                        .map(pat_to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

fn lit_to_string(lit: &Lit) -> String {
    match lit {
        Lit::Bool(b) => b.to_string(),
        Lit::Int(s) => s.clone(),
        Lit::Str(s) => {
            let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
            format!("\"{}\"", escaped)
        }
    }
}

#[derive(Copy, Clone)]
enum AccessKind {
    Copy,
    Move,
}

#[derive(Debug, Clone, Default)]
struct ClosureUsage {
    closure_capture_len: Option<usize>,
    fix_capture_len: Option<usize>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum IndexSourceKind {
    Direct,
    Nested,
}

#[derive(Debug, Clone)]
struct ClosureEnv {
    capture_names: Vec<String>,
}

#[derive(Debug, Clone)]
struct RecursorSignature {
    arg_types: Vec<MirType>,
    result_ty: MirType,
}

#[derive(Debug, Clone)]
struct RecursorSpec {
    adt_id: AdtId,
    arg_types: Vec<MirType>,
    result_ty: MirType,
    name: String,
}

impl RecursorSpec {
    fn impl_name(&self) -> String {
        format!("{}_impl", self.name)
    }
}

fn inductive_result_sort_is_prop(ty: &Term) -> bool {
    let mut current = ty;
    loop {
        match current {
            Term::Pi(_, body, _, _) => {
                current = body.as_ref();
            }
            Term::Sort(level) => return matches!(level, Level::Zero),
            _ => return false,
        }
    }
}

fn count_arity(ty: &std::rc::Rc<kernel::ast::Term>) -> usize {
    let mut arity = 0;
    let mut current = ty;
    while let kernel::ast::Term::Pi(_, body, _, _) = &**current {
        arity += 1;
        current = body;
    }
    arity
}

fn count_indices(ty: &std::rc::Rc<kernel::ast::Term>, num_params: usize) -> usize {
    let mut count: usize = 0;
    let mut current = ty;
    while let kernel::ast::Term::Pi(_, body, _, _) = &**current {
        count += 1;
        current = body;
    }
    count.saturating_sub(num_params)
}

fn sanitize_name(name: &str) -> String {
    crate::codegen::sanitize_name(name)
}

#[cfg(test)]
mod tests {
    use super::{codegen_program, TypedBody, TypedCodegenError, TypedCodegenReason, TypedProgram};
    use crate::types::{IdRegistry, MirType};
    use crate::{
        BasicBlockData, Body, BorrowKind, CallOperand, Constant, Literal, Local, LocalDecl,
        Operand, Place, PlaceElem, Rvalue, Statement, Terminator,
    };
    use kernel::ast::FunctionKind;
    use kernel::checker::Env;

    fn local(name: &str, ty: MirType) -> LocalDecl {
        LocalDecl::new(ty, Some(name.to_string()))
    }

    fn nat_const(value: u64) -> Operand {
        Operand::Constant(Box::new(Constant {
            literal: Literal::Nat(value),
            ty: MirType::Nat,
        }))
    }

    fn build_body(
        arg_count: usize,
        local_decls: Vec<LocalDecl>,
        statements: Vec<Statement>,
        terminator: Terminator,
    ) -> Body {
        let mut body = Body::new(arg_count);
        body.local_decls = local_decls;
        body.basic_blocks.push(BasicBlockData {
            statements,
            terminator: Some(terminator),
        });
        body
    }

    fn single_def_program(body: Body) -> TypedProgram {
        TypedProgram {
            defs: vec![TypedBody {
                name: "entry".to_string(),
                body,
                closure_base: 0,
            }],
            closures: Vec::new(),
            main_name: Some("entry".to_string()),
        }
    }

    fn reason_for_body(body: Body) -> TypedCodegenReason {
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let program = single_def_program(body);
        codegen_program(&env, &ids, &program)
            .expect_err("expected typed codegen error for malformed MIR")
            .reason
    }

    #[test]
    fn typed_codegen_reason_codes_are_stable() {
        assert_eq!(TypedCodegenReason::UnsupportedFnMut.code(), "TB001");
        assert_eq!(
            TypedCodegenReason::UnsupportedNonUnaryFunction.code(),
            "TB002"
        );
        assert_eq!(TypedCodegenReason::UnsupportedCallOperand.code(), "TB003");
        assert_eq!(
            TypedCodegenReason::UnsupportedProjectionAssignment.code(),
            "TB004"
        );
        assert_eq!(
            TypedCodegenReason::UnsupportedPlaceProjection.code(),
            "TB005"
        );
        assert_eq!(
            TypedCodegenReason::UnsupportedClosureEnvProjection.code(),
            "TB006"
        );
        assert_eq!(TypedCodegenReason::UnsupportedClosureType.code(), "TB007");
        assert_eq!(TypedCodegenReason::UnsupportedFixpointType.code(), "TB008");
        assert_eq!(
            TypedCodegenReason::UnsupportedPolymorphicFunctionValue.code(),
            "TB009"
        );
        assert_eq!(TypedCodegenReason::InternalInvariant.code(), "TB900");
    }

    #[test]
    fn typed_codegen_error_display_includes_reason_code() {
        let err = TypedCodegenError::unsupported(
            TypedCodegenReason::UnsupportedFnMut,
            "FnMut not supported in typed backend",
        );
        assert_eq!(
            err.to_string(),
            "[TB001] FnMut not supported in typed backend"
        );
    }

    #[test]
    fn typed_codegen_rejects_non_unary_function_shape_with_tb002() {
        let body = build_body(
            0,
            vec![
                local("_0", MirType::Unit),
                local(
                    "_1",
                    MirType::Fn(
                        FunctionKind::Fn,
                        Vec::new(),
                        vec![MirType::Nat, MirType::Nat],
                        Box::new(MirType::Nat),
                    ),
                ),
            ],
            Vec::new(),
            Terminator::Return,
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedNonUnaryFunction
        );
    }

    #[test]
    fn typed_codegen_rejects_invalid_call_operand_with_tb003() {
        let body = build_body(
            0,
            vec![local("_0", MirType::Unit), local("_1", MirType::Nat)],
            Vec::new(),
            Terminator::Call {
                func: CallOperand::Borrow(BorrowKind::Shared, Place::from(Local(1))),
                args: vec![nat_const(0)],
                destination: Place::from(Local(0)),
                target: None,
            },
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedCallOperand
        );
    }

    #[test]
    fn typed_codegen_rejects_projection_assignment_with_tb004() {
        let body = build_body(
            0,
            vec![local("_0", MirType::Unit), local("_1", MirType::Nat)],
            vec![Statement::Assign(
                Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Downcast(1), PlaceElem::Field(0)],
                },
                Rvalue::Use(nat_const(1)),
            )],
            Terminator::Return,
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedProjectionAssignment
        );
    }

    #[test]
    fn typed_codegen_rejects_invalid_place_projection_with_tb005() {
        let body = build_body(
            0,
            vec![local("_0", MirType::Unit), local("_1", MirType::Nat)],
            vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Field(0)],
                })),
            )],
            Terminator::Return,
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedPlaceProjection
        );
    }

    #[test]
    fn typed_codegen_rejects_invalid_closure_env_projection_with_tb006() {
        let body = build_body(
            2,
            vec![
                local("_0", MirType::Unit),
                local("_1", MirType::Unit),
                local("_2", MirType::Unit),
            ],
            vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Copy(Place {
                    local: Local(1),
                    projection: vec![PlaceElem::Deref],
                })),
            )],
            Terminator::Return,
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedClosureEnvProjection
        );
    }

    #[test]
    fn typed_codegen_rejects_invalid_closure_constant_type_with_tb007() {
        let body = build_body(
            0,
            vec![local("_0", MirType::Unit)],
            vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Closure(0, Vec::new()),
                    ty: MirType::Unit,
                }))),
            )],
            Terminator::Return,
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedClosureType
        );
    }

    #[test]
    fn typed_codegen_rejects_invalid_fix_constant_type_with_tb008() {
        let body = build_body(
            0,
            vec![local("_0", MirType::Unit)],
            vec![Statement::Assign(
                Place::from(Local(0)),
                Rvalue::Use(Operand::Constant(Box::new(Constant {
                    literal: Literal::Fix(0, Vec::new()),
                    ty: MirType::Unit,
                }))),
            )],
            Terminator::Return,
        );
        assert_eq!(
            reason_for_body(body),
            TypedCodegenReason::UnsupportedFixpointType
        );
    }

    #[test]
    fn typed_codegen_accepts_former_tb001_fnmut_type_shape() {
        let body = build_body(
            0,
            vec![
                local("_0", MirType::Unit),
                local(
                    "_1",
                    MirType::Fn(
                        FunctionKind::FnMut,
                        Vec::new(),
                        vec![MirType::Nat],
                        Box::new(MirType::Nat),
                    ),
                ),
            ],
            Vec::new(),
            Terminator::Return,
        );
        let env = Env::new();
        let ids = IdRegistry::from_env(&env);
        let program = single_def_program(body);
        let code = codegen_program(&env, &ids, &program)
            .expect("typed codegen should support former TB001 fnmut shape");
        assert!(!code.is_empty(), "typed backend should emit Rust code");
    }
}
