use im::vector;
use im::Vector;
use indexmap::{IndexMap, IndexSet};
use std::borrow::Borrow;
use std::fmt;
use std::rc::Rc;

use crate::ast::*;
use crate::error::SpannedError;
use crate::permission::*;
use crate::smt;
use crate::span::Spanned;

#[derive(Clone, Debug)]
pub struct LocalCtx {
    vars: IndexMap<Var, TermType>,
}

#[derive(Clone, Debug)]
pub struct ResourceCtx {
    pub perm: Permission,
    pub ins: IndexSet<ChanName>,
    pub outs: IndexSet<ChanName>,
}

impl LocalCtx {
    pub fn new() -> LocalCtx {
        LocalCtx {
            vars: IndexMap::new(),
        }
    }

    pub fn get(&self, var: impl Into<Var>) -> Option<&TermType> {
        self.vars.get(&var.into())
    }

    pub fn contains(&self, var: impl Into<Var>) -> bool {
        self.vars.contains_key(&var.into())
    }

    pub fn vars(&self) -> impl Iterator<Item = (&Var, &TermType)> {
        self.vars.iter()
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn insert(&mut self, var: impl Into<Var>, typ: impl Borrow<TermType>) -> &mut LocalCtx {
        self.vars.insert(var.into(), typ.borrow().clone());
        self
    }
}

impl ResourceCtx {
    pub fn new() -> ResourceCtx {
        ResourceCtx {
            perm: PermissionX::empty(),
            ins: IndexSet::new(),
            outs: IndexSet::new(),
        }
    }
}

impl BaseType {
    pub fn type_check(&self, _ctx: &Ctx) -> Result<(), String> {
        match self {
            BaseType::Bool => Ok(()),
            BaseType::Int => Ok(()),
            BaseType::BitVec(w) => {
                if *w > 0 {
                    Ok(())
                } else {
                    Err(format!("bit-width needs to be positive"))
                }
            }
        }
    }
}

impl MutTypeX {
    pub fn type_check(&self, ctx: &Ctx) -> Result<(), String> {
        match self {
            MutTypeX::Base(base) => base.type_check(ctx),
            MutTypeX::Array(t1, t2) => {
                if t1.is_int() || t1.is_bv() {
                    t2.type_check(ctx)
                } else {
                    Err(format!("type {} cannot be used as index type", t1))
                }
            }
        }
    }
}

impl MutReferenceIndex {
    /// Overapproximate a MutReferenceIndex from a term
    pub fn from_term(term: &Term) -> MutReferenceIndex {
        match &term.x {
            TermX::Int(i) => MutReferenceIndex::Int(*i),
            TermX::BitVec(i, w) => MutReferenceIndex::BitVec(*i, *w),
            _ => MutReferenceIndex::Unknown,
        }
    }

    /// Check if one index is subsumed by another:
    /// i <= * for any i: int
    /// * <= *
    pub fn is_subsumed_by(&self, other: &MutReferenceIndex) -> bool {
        match other {
            MutReferenceIndex::Int(..) => self == other,
            MutReferenceIndex::BitVec(..) => self == other,
            MutReferenceIndex::Unknown => true,
        }
    }

    pub fn has_base_type(&self, typ: &BaseType) -> bool {
        match self {
            MutReferenceIndex::Int(..) => typ.is_int(),
            MutReferenceIndex::BitVec(..) => typ.is_bv(),
            MutReferenceIndex::Unknown => true,
        }
    }

    /// * + any = *
    /// const + const = const
    pub fn add(&self, other: &MutReferenceIndex) -> Option<MutReferenceIndex> {
        match (self, other) {
            (MutReferenceIndex::Int(a), MutReferenceIndex::Int(b)) => {
                Some(MutReferenceIndex::Int(a + b))
            }
            // NOTE: bit_vec(a + b) = bit_vec(a) +bv bit_vec(b)
            (MutReferenceIndex::BitVec(a, w1), MutReferenceIndex::BitVec(b, w2)) if w1 == w2 => {
                Some(MutReferenceIndex::BitVec(a + b, *w1))
            }
            (_, MutReferenceIndex::Unknown) => Some(MutReferenceIndex::Unknown),
            (MutReferenceIndex::Unknown, _) => Some(MutReferenceIndex::Unknown),
            _ => None,
        }
    }
}

impl MutReferenceTypeX {
    /// Type check a mutable reference type
    /// and return the mutable type it refers to
    /// e.g.
    /// mut A: [[int]]
    /// then &A[1:][*] has type [int]
    pub fn type_check(&self, ctx: &Ctx) -> Result<MutType, String> {
        match self {
            MutReferenceTypeX::Base(m) => Ok(ctx
                .muts
                .get(m)
                .ok_or(format!("mutable `{}` does not exist", m))?
                .typ
                .clone()),

            MutReferenceTypeX::Index(t, i) => match t.type_check(ctx)?.borrow() {
                MutTypeX::Base(..) => Err(format!("cannot index into a base mutable type")),
                MutTypeX::Array(t1, t2) => {
                    if !i.has_base_type(t1) {
                        return Err(format!("incorrect index type"));
                    }
                    Ok(t2.clone())
                }
            },

            MutReferenceTypeX::Offset(t, i) => {
                let typ = t.type_check(ctx)?;
                match typ.borrow() {
                    MutTypeX::Base(..) => {
                        Err(format!("cannot take the slice of a base mutable type"))
                    }
                    MutTypeX::Array(t, ..) => {
                        if !i.has_base_type(t) {
                            return Err(format!("incorrect index type"));
                        }
                        Ok(typ.clone())
                    }
                }
            }
        }
    }

    /// Canonicalize a mutable reference type
    /// e.g.
    /// A[1..][2..][3] => A[6]
    /// A[1..][*..][3][2..][3..] => A[*][6..]
    ///
    /// In general, the canonical form is A[t1][t2]...[tn][t'..]
    /// where t1 ... tn, t' are * or constants
    pub fn canonicalize(ctx: &Ctx, typ: &MutReferenceType) -> Result<MutReferenceType, String> {
        match typ.borrow() {
            MutReferenceTypeX::Base(..) => match typ.type_check(ctx)?.borrow() {
                MutTypeX::Base(..) => Ok(typ.clone()),
                // If A is an array, rewrite A => A[0..]
                MutTypeX::Array(BaseType::Int, ..) => Ok(Rc::new(MutReferenceTypeX::Offset(
                    typ.clone(),
                    MutReferenceIndex::Int(0),
                ))),
                MutTypeX::Array(BaseType::BitVec(w), ..) => Ok(Rc::new(MutReferenceTypeX::Offset(
                    typ.clone(),
                    MutReferenceIndex::BitVec(0, *w),
                ))),
                _ => Err(format!("unsupported base reference type {}", typ)),
            },
            MutReferenceTypeX::Index(m, i) => {
                let m_canon = MutReferenceTypeX::canonicalize(ctx, m)?;
                match m_canon.borrow() {
                    // m[i2..][i] => m[i2 + i]
                    MutReferenceTypeX::Offset(m_canon, i2) => {
                        Ok(Rc::new(MutReferenceTypeX::Index(
                            m_canon.clone(),
                            i.add(i2)
                                .ok_or(format!("failed to add indices {} and {}", i, i2))?,
                        )))
                    }
                    _ => Ok(Rc::new(MutReferenceTypeX::Index(m_canon, i.clone()))),
                }
            }
            MutReferenceTypeX::Offset(m, i) => {
                let m_canon = MutReferenceTypeX::canonicalize(ctx, m)?;
                match m_canon.borrow() {
                    // m[i2..][i..] => m[i2 + i..]
                    MutReferenceTypeX::Offset(m_canon, i2) => {
                        Ok(Rc::new(MutReferenceTypeX::Offset(
                            m_canon.clone(),
                            i.add(i2)
                                .ok_or(format!("failed to add indices {} and {}", i, i2))?,
                        )))
                    }
                    _ => Ok(Rc::new(MutReferenceTypeX::Offset(m_canon, i.clone()))),
                }
            }
        }
    }

    /// Check if self is a subtype of other
    /// e.g.
    /// A[1..] <= A[*..]
    /// A[1..3] <= A[*..*]
    ///
    /// However, for simplicity, we currently do not
    /// consider subtypings like A[1..][1..] <= A[2..]
    /// i.e. both references need to be of the same "shape"
    pub fn is_subtype(ctx: &Ctx, this: &MutReferenceType, other: &MutReferenceType) -> bool {
        let this_canon = MutReferenceTypeX::canonicalize(ctx, this);
        let other_canon = MutReferenceTypeX::canonicalize(ctx, other);
        match (
            this_canon.as_ref().map(|t| t.as_ref()),
            other_canon.as_ref().map(|t| t.as_ref()),
        ) {
            (Ok(MutReferenceTypeX::Base(n1)), Ok(MutReferenceTypeX::Base(n2))) => n1 == n2,
            (Ok(MutReferenceTypeX::Index(m1, i1)), Ok(MutReferenceTypeX::Index(m2, i2)))
            | (Ok(MutReferenceTypeX::Offset(m1, i1)), Ok(MutReferenceTypeX::Offset(m2, i2))) => {
                m1 == m2 || MutReferenceTypeX::is_subtype(ctx, m1, m2) && i1.is_subsumed_by(i2)
            }
            _ => false,
        }
    }

    /// * => fresh variable
    /// constant => constant
    pub fn concretize_index(
        index: &MutReferenceIndex,
        expected: &BaseType,
        local: &mut LocalCtx,
    ) -> Term {
        match index {
            MutReferenceIndex::Int(i) => TermX::int(*i),
            MutReferenceIndex::BitVec(i, w) => TermX::bit_vec(*i, *w),
            MutReferenceIndex::Unknown => {
                let fresh_var: Var = format!("*{}", local.len()).into();
                local.insert(&fresh_var, TermTypeX::base(expected));
                TermX::var(fresh_var)
            }
        }
    }

    /// Generate a concrete mutable reference
    /// from a mutable reference type
    /// with all unknowns (*) replaced by free variables
    pub fn concretize(&self, ctx: &Ctx, local: &mut LocalCtx) -> Result<MutReference, String> {
        match self {
            MutReferenceTypeX::Base(n) => Ok(Spanned::new(MutReferenceX::Base(n.clone()))),
            MutReferenceTypeX::Index(m, i) =>
            // TODO: This is a bit inefficient, visiting m twice
            {
                match m.type_check(ctx)?.borrow() {
                    MutTypeX::Base(..) => unreachable!(),
                    MutTypeX::Array(index_type, ..) => Ok(Spanned::new(MutReferenceX::Index(
                        m.concretize(ctx, local)?,
                        Self::concretize_index(i, index_type, local),
                    ))),
                }
            }
            MutReferenceTypeX::Offset(m, i) => match m.type_check(ctx)?.borrow() {
                MutTypeX::Base(..) => unreachable!(),
                MutTypeX::Array(index_type, ..) => Ok(Spanned::new(MutReferenceX::Slice(
                    m.concretize(ctx, local)?,
                    Some(Self::concretize_index(&i, index_type, local)),
                    None,
                ))),
            },
        }
    }
}

impl TermTypeX {
    /// Checks if self <= other in subtyping
    pub fn is_subtype(&self, ctx: &Ctx, other: &TermTypeX) -> bool {
        match self {
            TermTypeX::Base(t) => {
                if let TermTypeX::Base(other) = other {
                    return t == other;
                } else {
                    false
                }
            }
            TermTypeX::Ref(refs1) => {
                if let TermTypeX::Ref(refs2) = other {
                    // Each type in refs1 is a subtype of some type in ref2
                    refs1.iter().all(|ref_typ1| {
                        refs2
                            .iter()
                            .any(|ref_typ2| MutReferenceTypeX::is_subtype(ctx, ref_typ1, ref_typ2))
                    })
                } else {
                    false
                }
            }
        }
    }

    pub fn type_check(&self, ctx: &Ctx) -> Result<(), String> {
        match self {
            TermTypeX::Base(t) => t.type_check(ctx),
            TermTypeX::Ref(..) => {
                self.get_mut_type(ctx)?;
                Ok(())
            }
        }
    }

    /// Get corresponding mutable type if the term type is a mutable reference type
    pub fn get_mut_type(&self, ctx: &Ctx) -> Result<(MutType, Vector<MutReferenceType>), String> {
        match self {
            TermTypeX::Base(t) => Err(format!("dereferencing base type {}", t)),
            TermTypeX::Ref(refs) => {
                if refs.len() == 0 {
                    return Err(format!("Empty reference type {}", self));
                }
                let mut_typs = refs
                    .iter()
                    .map(|r| r.type_check(ctx))
                    .collect::<Result<IndexSet<_>, _>>()?;

                if mut_typs.len() != 1 {
                    return Err(format!(
                        "reference to mutable(s) with inconsistent types {{ {} }}",
                        mut_typs
                            .iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                    ));
                }

                Ok((mut_typs.first().unwrap().clone(), refs.clone()))
            }
        }
    }
}

impl MutReferenceX {
    /// Type check and then get the mutable type the mutable reference should refer to
    /// e.g. mut A: [[int]] => A[a:b][c].type_check() = [int]
    pub fn type_check(
        mut_ref: &MutReference,
        ctx: &Ctx,
        local: &LocalCtx,
    ) -> Result<MutType, SpannedError> {
        match &mut_ref.x {
            MutReferenceX::Base(n) => Ok(ctx
                .muts
                .get(n)
                .ok_or(SpannedError::spanned(
                    &mut_ref.span,
                    format!("mutable `{}` not declared", n),
                ))?
                .typ
                .clone()),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                let (mut_type, _) = typ
                    .get_mut_type(ctx)
                    .map_err(|msg| SpannedError::spanned(&mut_ref.span, msg))?;
                Ok(mut_type)
            }
            MutReferenceX::Index(m, t) => {
                match MutReferenceX::type_check(m, ctx, local)?.borrow() {
                    MutTypeX::Base(..) => {
                        SpannedError::spanned_err(&mut_ref.span, format!("indexing into base type"))
                    }
                    MutTypeX::Array(index_type, typ) => {
                        let t_type = TermX::type_check(t, ctx, local)?;
                        if !t_type.is_base(index_type) {
                            return SpannedError::spanned_err(
                                &mut_ref.span,
                                format!(
                                    "unexpected index type: expecting {}, got {}",
                                    index_type, t_type
                                ),
                            );
                        }
                        Ok(typ.clone())
                    }
                }
            }
            MutReferenceX::Slice(m, t1, t2) => {
                let typ = MutReferenceX::type_check(m, ctx, local)?;
                match typ.borrow() {
                    MutTypeX::Base(..) => {
                        SpannedError::spanned_err(&mut_ref.span, format!("slicing into base type"))
                    }
                    MutTypeX::Array(index_type, ..) => {
                        if let Some(t1) = t1 {
                            let t1_type = TermX::type_check(t1, ctx, local)?;
                            if !t1_type.is_base(index_type) {
                                return SpannedError::spanned_err(
                                    &mut_ref.span,
                                    format!(
                                        "unexpected index type: expecting {}, got {}",
                                        index_type, t1_type
                                    ),
                                );
                            }
                        }

                        if let Some(t2) = t2 {
                            let t2_type = TermX::type_check(t2, ctx, local)?;
                            if !t2_type.is_base(index_type) {
                                return SpannedError::spanned_err(
                                    &mut_ref.span,
                                    format!(
                                        "unexpected index type: expecting {}, got {}",
                                        index_type, t2_type
                                    ),
                                );
                            }
                        }
                        Ok(typ)
                    }
                }
            }
        }
    }

    /// Overapproximate the mutable reference as a set of mutable reference types
    pub fn approximate(
        mut_ref: &MutReference,
        ctx: &Ctx,
        local: &LocalCtx,
    ) -> Result<Vector<MutReferenceType>, SpannedError> {
        match &mut_ref.x {
            MutReferenceX::Base(n) => Ok(vector![Rc::new(MutReferenceTypeX::Base(n.clone()))]),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                let (_, base_refs) = typ
                    .get_mut_type(ctx)
                    .map_err(|msg| SpannedError::spanned(&mut_ref.span, msg))?;
                Ok(base_refs)
            }
            MutReferenceX::Index(m, t) => {
                let refs = MutReferenceX::approximate(m, ctx, local)?;
                Ok(refs
                    .iter()
                    .map(|r| {
                        Rc::new(MutReferenceTypeX::Index(
                            r.clone(),
                            MutReferenceIndex::from_term(t),
                        ))
                    })
                    .collect())
            }
            MutReferenceX::Slice(m, t, ..) => {
                let refs = MutReferenceX::approximate(m, ctx, local)?;

                if let Some(t) = t {
                    Ok(refs
                        .iter()
                        .map(|r|
                            // [t1..t2] => [^(t1)..]
                            Rc::new(MutReferenceTypeX::Offset(r.clone(), MutReferenceIndex::from_term(&t))))
                        .collect())
                } else {
                    Ok(refs)
                }
            }
        }
    }

    /// Concretize a mutable reference with potentially a deref at the base
    /// (if there is no deref, the result should be identical to the original mutable reference)
    pub fn concretize(
        mut_ref: &MutReference,
        ctx: &Ctx,
        local: &mut LocalCtx,
    ) -> Result<Vec<MutReference>, SpannedError> {
        match &mut_ref.x {
            MutReferenceX::Base(..) => Ok(vec![mut_ref.clone()]),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                let (_, base_refs) = typ
                    .get_mut_type(ctx)
                    .map_err(|msg| SpannedError::spanned(&mut_ref.span, msg))?;
                Ok(base_refs
                    .iter()
                    .map(|r| r.concretize(ctx, local))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|msg| SpannedError::spanned(&mut_ref.span, msg))?)
            }
            MutReferenceX::Index(m, t) => Ok(Self::concretize(m, ctx, local)?
                .into_iter()
                .map(|m| Spanned::new(MutReferenceX::Index(m, t.clone())))
                .collect()),
            MutReferenceX::Slice(m, t1, t2) => Ok(Self::concretize(m, ctx, local)?
                .into_iter()
                .map(|m| Spanned::new(MutReferenceX::Slice(m, t1.clone(), t2.clone())))
                .collect()),
        }
    }
}

impl TermX {
    /// Checks the type of a term under a local context
    /// Returns either the type or an error message
    pub fn type_check(term: &Term, ctx: &Ctx, local: &LocalCtx) -> Result<TermType, SpannedError> {
        match &term.x {
            TermX::Var(var) => Ok(local
                .vars
                .get(var)
                .ok_or(SpannedError::spanned(
                    &term.span,
                    format!("variable `{}` not in context", var),
                ))?
                .clone()),
            TermX::Const(c) => ctx
                .consts
                .get(c)
                .map(|decl| TermTypeX::base(&decl.typ))
                .ok_or(SpannedError::spanned(
                    &term.span,
                    format!("constant `{}` not defined", c),
                )),
            TermX::Bool(_) => Ok(TermTypeX::bool()),
            TermX::Int(_) => Ok(TermTypeX::int()),
            TermX::BitVec(_, w) => Ok(TermTypeX::bit_vec(*w)),
            TermX::Ref(m) => {
                MutReferenceX::type_check(m, ctx, local)?;
                let refs = MutReferenceX::approximate(m, ctx, local)?;
                Ok(Rc::new(TermTypeX::Ref(refs)))
            }
            TermX::Add(t1, t2) | TermX::Mul(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_int() {
                    Ok(typ1.clone())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
            TermX::BVAdd(t1, t2) | TermX::BVMul(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_bv() {
                    Ok(typ1.clone())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Less(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_int() {
                    Ok(TermTypeX::bool())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
            TermX::BVULT(t1, t2) | TermX::BVSLT(t1, t2) | TermX::BVSGT(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_bv() {
                    Ok(TermTypeX::bool())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
            TermX::And(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_bool() {
                    Ok(TermTypeX::bool())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Equal(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && !typ1.is_ref() {
                    Ok(TermTypeX::bool())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Not(t) => {
                if TermX::type_check(t, ctx, local)?.is_bool() {
                    Ok(TermTypeX::bool())
                } else {
                    SpannedError::spanned_err(&term.span, format!("incorrect subterm type"))
                }
            }
        }
    }
}

impl PermissionX {
    pub fn type_check(perm: &Permission, ctx: &Ctx, local: &LocalCtx) -> Result<(), SpannedError> {
        match &perm.x {
            PermissionX::Empty => Ok(()),
            PermissionX::Add(p1, p2) => {
                PermissionX::type_check(p1, ctx, local).and(PermissionX::type_check(p2, ctx, local))
            }
            PermissionX::Sub(p1, p2) => {
                PermissionX::type_check(p1, ctx, local).and(PermissionX::type_check(p2, ctx, local))
            }
            PermissionX::Ite(t, p1, p2) => {
                if !TermX::type_check(t, ctx, local)?.is_bool() {
                    SpannedError::spanned_err(
                        &perm.span,
                        format!("permission if condition is not of type bool"),
                    )
                } else {
                    PermissionX::type_check(p1, ctx, local)?;
                    PermissionX::type_check(p2, ctx, local)?;
                    Ok(())
                }
            }
            // TODO: should we allow deref in permission?
            PermissionX::Fraction(_, mut_ref) => {
                MutReferenceX::type_check(mut_ref, ctx, local).map(|_| ())
            }
            PermissionX::Var(v, terms) => {
                let decl = ctx.perms.get(v).ok_or(SpannedError::spanned(
                    &perm.span,
                    format!("permission variable `{}` not declared", v),
                ))?;

                if decl.param_typs.len() != terms.len() {
                    return SpannedError::spanned_err(
                        &perm.span,
                        format!("unmatched number of arguments provided for permission variable `{}`: expect {}, given {}", v, decl.param_typs.len(), terms.len()),
                    );
                }

                for (typ, term) in decl.param_typs.iter().zip(terms) {
                    if !TermX::type_check(term, ctx, local)?.is_subtype(ctx, &TermTypeX::base(typ))
                    {
                        return SpannedError::spanned_err(
                            &perm.span,
                            format!("unmatched argument type for permission variable `{}`", v),
                        );
                    }
                }
                Ok(())
            }
        }
    }
}

impl ProcX {
    /// Type check a process and keep track
    /// of a list of permission constraints
    /// If the type checking fails, the permission
    /// constraints might still be updated
    fn type_check_inplace(
        proc: &Proc,
        ctx: &Ctx,
        local: &mut LocalCtx,
        resources: &mut ResourceCtx,
        path_conditions: &mut Vector<Term>,
        constraints: &mut Vector<PermJudgment>,
    ) -> Result<(), SpannedError> {
        match &proc.x {
            ProcX::Skip => Ok(()),
            ProcX::Send(c, t, k) => {
                let chan_decl = ctx.chans.get(c).ok_or(SpannedError::spanned(
                    &proc.span,
                    format!("channel `{}` does not exist", c),
                ))?;

                let t_typ = TermX::type_check(t, ctx, local)?;
                if !t_typ.is_subtype(ctx, &chan_decl.typ) {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!(
                            "unmatched send channel type: expecting {}, got {}",
                            chan_decl.typ, t_typ
                        ),
                    );
                }

                // Output resource should be in the resouce context
                if !resources.outs.contains(c) {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("resouce `output {}` not declared", c),
                    );
                }

                // Need to spend the permission required by the channel
                let send_perm = PermissionX::substitute_one(&chan_decl.perm, &chan_decl.name, t);
                constraints.push_back(Rc::new(PermJudgmentX {
                    local: local.clone(),
                    local_constraints: path_conditions.clone(),
                    perm_constraint: PermConstraintX::less_eq(&send_perm, &resources.perm),
                }));
                resources.perm = PermissionX::sub(&resources.perm, &send_perm);

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, resources, path_conditions, constraints)
            }
            ProcX::Recv(c, v, k) => {
                let chan_decl = ctx.chans.get(c).ok_or(SpannedError::spanned(
                    &proc.span,
                    format!("channel `{}` does not exist", c),
                ))?;

                // Input resource should be in the resouce context
                if !resources.ins.contains(c) {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("resouce `input {}` not declared", c),
                    );
                }

                // Receive the permission contained in the channel
                let recv_perm =
                    PermissionX::substitute_one(&chan_decl.perm, &chan_decl.name, &TermX::var(v));
                resources.perm = PermissionX::add(&resources.perm, &recv_perm);

                // Receive a new variable
                if local.contains(v) {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("shadowing of local variable `{}` not supported", v),
                    );
                }
                if ctx.consts.contains_key(&Const::from(v)) {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("shadowing of constant `{}` not supported", v),
                    );
                }
                local.insert(v, &chan_decl.typ);

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, resources, path_conditions, constraints)
            }
            ProcX::Write(m, t, k) => {
                // Check t matches the type of the reference
                let t_typ = TermX::type_check(t, ctx, local)?;

                if let MutTypeX::Base(base) = MutReferenceX::type_check(m, ctx, local)?.borrow() {
                    if !t_typ.is_subtype(ctx, &TermTypeX::base(base)) {
                        return SpannedError::spanned_err(
                            &proc.span,
                            format!(
                                "write type is different from mutable type: expect {}, got {}",
                                t_typ, base
                            ),
                        );
                    }
                } else {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("cannot write to a non-base-typed mutable reference"),
                    );
                }

                // Check that we have suitable write permission
                // (for all possibly referenced mutables)
                if !m.has_deref() {
                    constraints.push_back(Rc::new(PermJudgmentX {
                        local: local.clone(),
                        local_constraints: path_conditions.clone(),
                        perm_constraint: PermConstraintX::has_write(&m, &resources.perm),
                    }));
                } else {
                    let mut local_copy = local.clone(); // need to host the extra fresh variables for unknowns (*)
                    for concrete_ref in MutReferenceX::concretize(m, ctx, &mut local_copy)? {
                        constraints.push_back(Rc::new(PermJudgmentX {
                            local: local_copy.clone(),
                            local_constraints: path_conditions.clone(),
                            perm_constraint: PermConstraintX::has_write(
                                &concrete_ref,
                                &resources.perm,
                            ),
                        }));
                    }
                }

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, resources, path_conditions, constraints)
            }
            ProcX::Read(m, v, k) => {
                // Get the return type of the read
                let mut_typ = MutReferenceX::type_check(m, ctx, local)?;

                // Check that we have suitable read permission
                // (for all possibly referenced mutables)
                if !m.has_deref() {
                    constraints.push_back(Rc::new(PermJudgmentX {
                        local: local.clone(),
                        local_constraints: path_conditions.clone(),
                        perm_constraint: PermConstraintX::has_read(m, &resources.perm),
                    }));
                } else {
                    let mut local_copy = local.clone(); // need to host the extra fresh variables for unknowns (*)
                    for concrete_ref in MutReferenceX::concretize(m, ctx, &mut local_copy)? {
                        constraints.push_back(Rc::new(PermJudgmentX {
                            local: local_copy.clone(),
                            local_constraints: path_conditions.clone(),
                            perm_constraint: PermConstraintX::has_read(
                                &concrete_ref,
                                &resources.perm,
                            ),
                        }));
                    }
                }

                // Update local context with new binding
                if let MutTypeX::Base(m_base) = mut_typ.borrow() {
                    // Add read variable into context
                    if local.contains(v) {
                        return SpannedError::spanned_err(
                            &proc.span,
                            format!("shadowing of local variable `{}` not supported", v),
                        );
                    }
                    if ctx.consts.contains_key(&Const::from(v)) {
                        return SpannedError::spanned_err(
                            &proc.span,
                            format!("shadowing of constant `{}` not supported", v),
                        );
                    }
                    local.insert(v, TermTypeX::base(m_base));
                } else {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("cannot read from a non-base-typed mutable reference"),
                    );
                }

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, resources, path_conditions, constraints)
            }
            ProcX::Ite(t, k1, k2) => {
                if !TermX::type_check(t, ctx, local)?.is_bool() {
                    return SpannedError::spanned_err(
                        &proc.span,
                        format!("if condition not of type bool"),
                    );
                }

                let mut local_copy = local.clone();
                let mut resources_copy = resources.clone();
                let mut path_conditions_copy = path_conditions.clone();

                // Push respective path conditions
                path_conditions.push_back(t.clone());
                path_conditions_copy.push_back(TermX::not(t));

                ProcX::type_check_inplace(k1, ctx, local, resources, path_conditions, constraints)?;
                ProcX::type_check_inplace(
                    k2,
                    ctx,
                    &mut local_copy,
                    &mut resources_copy,
                    &mut path_conditions_copy,
                    constraints,
                )
            }

            // P <args> has the same typing rules as P <args> || skip
            ProcX::Call(..) => ProcX::type_check_inplace(
                &ProcX::par(proc, &ProcX::skip()),
                ctx,
                local,
                resources,
                path_conditions,
                constraints,
            ),

            // TODO: currently, we only allow process calls to
            // be the LHS of a parallel composition.
            // Because the split of permissions need to be explicitly specified
            ProcX::Par(k1, k2) => {
                if let ProcX::Call(name, args) = &k1.x {
                    let proc_decl = ctx.procs.get(name).ok_or(SpannedError::spanned(
                        &k1.span,
                        format!("process `{}` does not exist", name),
                    ))?;

                    // Check argument types are correct
                    if args.len() != proc_decl.params.len() {
                        return SpannedError::spanned_err(
                            &k1.span,
                            format!("mismatched number of arguments"),
                        );
                    }

                    // Check argument types and construct param -> arg mapping
                    let mut subst = IndexMap::new();

                    for (arg, param) in args.iter().zip(&proc_decl.params) {
                        let typ = TermX::type_check(arg, ctx, local)?;
                        if !typ.is_subtype(ctx, &param.typ) {
                            return SpannedError::spanned_err(
                                &k1.span,
                                format!(
                                    "unmatched argument type: expecting {}, got {}",
                                    param.typ, typ
                                ),
                            );
                        }
                        subst.insert(param.name.clone(), arg.clone());
                    }

                    // Check sufficient resources are provided
                    for res in &proc_decl.res {
                        match &res.x {
                            ProcResourceX::Perm(p) => {
                                // Should have enough resource to call the process
                                let p_subst = PermissionX::substitute(p, &subst);
                                constraints.push_back(Rc::new(PermJudgmentX {
                                    local: local.clone(),
                                    local_constraints: path_conditions.clone(),
                                    perm_constraint: PermConstraintX::less_eq(
                                        &p_subst,
                                        &resources.perm,
                                    ),
                                }));
                                resources.perm = PermissionX::sub(&resources.perm, &p_subst);
                            }

                            // Check that input/output channels are within the resource context
                            ProcResourceX::Input(name) => {
                                if !resources.ins.shift_remove(name) {
                                    return SpannedError::spanned_err(
                                        &k1.span,
                                        format!(
                                            "required resource `input {}` not present at call site",
                                            name
                                        ),
                                    );
                                }
                            }

                            ProcResourceX::Output(name) => {
                                if !resources.outs.shift_remove(name) {
                                    return SpannedError::spanned_err(&k1.span, format!("required resource `output {}` not present at call site", name));
                                }
                            }
                        }
                    }

                    // Continue checking the rest of the parallel composition
                    ProcX::type_check_inplace(
                        k2,
                        ctx,
                        local,
                        resources,
                        path_conditions,
                        constraints,
                    )
                } else {
                    SpannedError::spanned_err(
                        &proc.span,
                        format!("currently only process calls are allowed to be the LHS of ||"),
                    )
                }
            }
        }
    }
}

impl MutDeclX {
    pub fn type_check(decl: &MutDecl, ctx: &Ctx) -> Result<(), SpannedError> {
        decl.typ
            .type_check(ctx)
            .map_err(|msg| SpannedError::spanned(&decl.span, msg))
    }
}

impl ChanDeclX {
    pub fn type_check(decl: &ChanDecl, ctx: &Ctx) -> Result<(), SpannedError> {
        decl.typ
            .type_check(ctx)
            .map_err(|msg| SpannedError::spanned(&decl.span, msg))?;
        PermissionX::type_check(
            &decl.perm,
            ctx,
            &LocalCtx {
                vars: IndexMap::from([(Var::from(&decl.name), decl.typ.clone())]),
            },
        )
    }
}

impl ProcResourceX {
    // Type check a resource and update the resource context if successful
    pub fn type_check_inplace(
        res: &ProcResource,
        ctx: &Ctx,
        local: &LocalCtx,
        resources: &mut ResourceCtx,
    ) -> Result<(), SpannedError> {
        match &res.x {
            ProcResourceX::Perm(perm) => {
                PermissionX::type_check(perm, ctx, &local)?;
                resources.perm = PermissionX::add(&resources.perm, perm);
            }
            ProcResourceX::Input(name) => {
                if !ctx.chans.contains_key(name) {
                    return SpannedError::spanned_err(
                        &res.span,
                        format!("channel `{}` does not exist", name),
                    );
                }

                if !resources.ins.insert(name.clone()) {
                    return SpannedError::spanned_err(
                        &res.span,
                        format!("duplicate `input {}`", name),
                    );
                }
            }
            ProcResourceX::Output(name) => {
                if !ctx.chans.contains_key(name) {
                    return SpannedError::spanned_err(
                        &res.span,
                        format!("channel `{}` does not exist", name),
                    );
                }

                if !resources.outs.insert(name.clone()) {
                    return SpannedError::spanned_err(
                        &res.span,
                        format!("duplicate `output {}`", name),
                    );
                }
            }
        }
        Ok(())
    }

    // Type check a resource and update the resource context if successful
    pub fn type_check(
        res: &Vector<ProcResource>,
        ctx: &Ctx,
        local: &LocalCtx,
    ) -> Result<ResourceCtx, SpannedError> {
        let mut resources = ResourceCtx::new();
        for r in res {
            ProcResourceX::type_check_inplace(r, ctx, local, &mut resources)?;
        }
        Ok(resources)
    }
}

impl ProcParamX {
    pub fn type_check(params: &Vector<ProcParam>, ctx: &Ctx) -> Result<LocalCtx, SpannedError> {
        let mut local = LocalCtx::new();
        for param in params {
            param
                .typ
                .type_check(ctx)
                .map_err(|msg| SpannedError::spanned(&param.span, msg))?;
            local.insert(param.name.clone(), param.typ.clone());
        }
        Ok(local)
    }
}

impl ProcDeclX {
    pub fn type_check(decl: &ProcDecl, ctx: &Ctx) -> Result<Vector<PermJudgment>, SpannedError> {
        let mut local = ProcParamX::type_check(&decl.params, ctx)?;
        let mut resources = ProcResourceX::type_check(&decl.res, ctx, &local)?;
        let mut constraints = Vector::new();
        ProcX::type_check_inplace(
            &decl.body,
            ctx,
            &mut local,
            &mut resources,
            &mut Vector::new(),
            &mut constraints,
        )?;
        Ok(constraints)
    }
}

pub enum PermCheckMode {
    /// Check validity of all permission constraints
    /// assuming they do not have free permission variables
    Check(smt::Solver),

    /// Infer permission variables using a synthesis solver
    Infer(smt::Solver, PermInferOptions),

    /// Do not check permissions
    None,
}

impl Ctx {
    /// Type-check everything in a context
    pub fn type_check(&self, mode: &mut PermCheckMode) -> Result<(), SpannedError> {
        // Mutables types are base types and are always correct

        for decl in self.muts.values() {
            MutDeclX::type_check(decl, self)?;
        }

        for decl in self.chans.values() {
            ChanDeclX::type_check(decl, self)?;
        }

        let mut all_constraints = Vec::new();
        let mut all_perm_valid = true;

        // Check process types
        for decl in self.procs.values() {
            let constraints = ProcDeclX::type_check(decl, self)?;

            println!("permission constraints for `{}`:", decl.name);
            for constraint in &constraints {
                // In check mode, we can check each permission constraint separately
                if let PermCheckMode::Check(solver) = mode {
                    if constraint.check_validity(self, solver)? {
                        println!("  valid: {}", constraint)
                    } else {
                        println!("  not valid: {}", constraint);
                        all_perm_valid = false;
                    }
                } else {
                    println!("  {}", constraint);
                }
            }

            all_constraints.extend(constraints);
        }

        // In infer mode, we need to collect all constraints before solving
        // for permission variables
        if let PermCheckMode::Infer(solver, options) = mode {
            match PermJudgmentX::infer_perm_var(all_constraints, options, self, solver)? {
                Some(model) => {
                    println!("inferred permission variables: {}", model);
                }
                None => {
                    println!("fail to infer permission variables");
                    all_perm_valid = false;
                }
            }
        }

        if all_perm_valid {
            Ok(())
        } else {
            SpannedError::new_err(format!("type checking failed"))
        }
    }
}

impl fmt::Display for LocalCtx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (v, t)) in self.vars().enumerate() {
            if i == 0 {
                write!(f, "{}: {}", v, t)?;
            } else {
                write!(f, ", {}: {}", v, t)?;
            }
        }
        write!(f, "}}")
    }
}
