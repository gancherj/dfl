use std::borrow::Borrow;
use std::fmt;
use std::rc::Rc;
use im::Vector;
use indexmap::{IndexMap, IndexSet};

use crate::ast::*;
use crate::permission::*;
use crate::smt;
use crate::span::Error;
use crate::span::Spanned;

/**
 * Type checking:
 * 1. Term is well-typed
 * 2. Permission is well-typed
 * 3. Process is well-typed in channel usage
 * 4. Process is well-typed in permissions (requires SMT)
 */

#[derive(Clone, Debug)]
pub struct LocalCtx {
    pub vars: IndexMap<Var, TermType>,
}

#[derive(Clone, Debug)]
pub struct ResourceCtx {
    pub perm: Permission,
    pub ins: IndexSet<ChanName>,
    pub outs: IndexSet<ChanName>,
}

impl fmt::Display for LocalCtx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (v, t)) in self.vars.iter().enumerate() {
            if i == 0 {
                write!(f, "{}: {}", v, t)?;
            } else {
                write!(f, ", {}: {}", v, t)?;
            }
        }
        write!(f, "}}")
    }
}

impl BaseType {
    /// Checks if self <= other in subtyping
    pub fn is_subtype(&self, other: &BaseType) -> bool {
        self == other
    }

    pub fn type_check(&self, _ctx: &Ctx) -> Result<(), String> {
        // Just a placeholder in case we need more base types
        Ok(())
    }
}

impl MutReferenceIndex {
    /// Overapproximate a MutReferenceIndex from a term
    pub fn from_term(term: &Term) -> MutReferenceIndex {
        match &term.x {
            TermX::Int(i) => MutReferenceIndex::Const(*i),
            _ => MutReferenceIndex::Unknown,
        }
    }

    // i <= * for any i: int
    pub fn is_subsumed_by(&self, other: &MutReferenceIndex) -> bool {
        match other {
            MutReferenceIndex::Const(..) => self == other,
            MutReferenceIndex::Unknown => true,
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
            MutReferenceTypeX::Base(m) =>
                Ok(ctx.muts.get(m).ok_or(format!("mutable `{}` does not exist", m))?.typ.clone()),

            MutReferenceTypeX::Index(t, ..) =>
                match t.type_check(ctx)?.borrow() {
                    MutTypeX::Base(..) => Err(format!("cannot index into a base mutable type")),
                    MutTypeX::Array(t) => Ok(t.clone()),
                }
    
            MutReferenceTypeX::Slice(t, ..) => {
                let typ = t.type_check(ctx)?;
                match typ.borrow() {
                    MutTypeX::Base(..) => Err(format!("cannot take the slice of a base mutable type")),
                    MutTypeX::Array(..) => Ok(typ.clone()),
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
    pub fn is_subtype(&self, other: &MutReferenceType) -> bool {
        match (self, &other.borrow()) {
            (MutReferenceTypeX::Base(n1), MutReferenceTypeX::Base(n2)) => n1 == n2,
            (MutReferenceTypeX::Index(m1, i1), MutReferenceTypeX::Index(m2, i2)) =>
                m1.is_subtype(m2) && i1.is_subsumed_by(i2),
            (MutReferenceTypeX::Slice(m1, i1, j1), MutReferenceTypeX::Slice(m2, i2, j2)) =>
                m1.is_subtype(m2) &&
                match (i1, i2) {
                    (None, None) => true,
                    (Some(i1), Some(i2)) => i1.is_subsumed_by(i2),
                    _ => false,
                } &&
                match (j1, j2) {
                    (None, None) => true,
                    (Some(j1), Some(j2)) => j1.is_subsumed_by(j2),
                    _ => false,
                },
            _ => false,
        }
    }

    /// * => fresh variable
    /// constant => constant
    pub fn concretize_index(index: &MutReferenceIndex, local: &mut LocalCtx) -> Term {
        match index {
            MutReferenceIndex::Const(i) => TermX::int(*i),
            MutReferenceIndex::Unknown => {
                let fresh_var = format!("*{}", local.vars.len());
                local.vars.insert(fresh_var.as_str().into(), TermTypeX::int());
                TermX::var(fresh_var)
            },
        }
    }

    /// Generate a concrete mutable reference
    /// from a mutable reference type
    /// with all unknowns (*) replaced by free variables
    pub fn concretize(&self, local: &mut LocalCtx) -> MutReference {
        match self {
            MutReferenceTypeX::Base(n) => Spanned::new(MutReferenceX::Base(n.clone())),
            MutReferenceTypeX::Index(m, i) =>
                Spanned::new(MutReferenceX::Index(m.concretize(local), Self::concretize_index(i, local))),
            MutReferenceTypeX::Slice(m, i1, i2) =>
                Spanned::new(MutReferenceX::Slice(
                    m.concretize(local),
                    i1.clone().map(|i| Self::concretize_index(&i, local)),
                    i2.clone().map(|i| Self::concretize_index(&i, local)),
                )),
        }
    }
}

impl TermTypeX {
    /// Checks if self <= other in subtyping
    pub fn is_subtype(&self, other: &TermTypeX) -> bool {
        match self {
            TermTypeX::Base(t) =>
                if let TermTypeX::Base(other) = other {
                    return t.is_subtype(other)
                } else {
                    false
                }
            TermTypeX::Ref(refs1) =>
                if let TermTypeX::Ref(refs2) = other {
                    // Each type in refs1 is a subtype of some type in ref2
                    refs1.iter().all(|ref_typ1|
                        refs2.iter().any(|ref_typ2| ref_typ1.is_subtype(ref_typ2)))
                } else {
                    false
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
    pub fn get_mut_type(&self, ctx: &Ctx) -> Result<(MutType, Vec<MutReferenceType>), String> {
        match self {
            TermTypeX::Base(t) => Err(format!("dereferencing base type {}", t)),
            TermTypeX::Ref(refs) => {
                if refs.len() == 0 {
                    return Err(format!("Empty reference type {}", self));
                }
                let mut_typs = refs.iter().map(|r| r.type_check(ctx)).collect::<Result<IndexSet<_>, _>>()?;

                if mut_typs.len() != 1 {
                    return Err(format!(
                        "reference to mutable(s) with inconsistent types {{ {} }}",
                        mut_typs.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", "),
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
    pub fn type_check(mut_ref: &MutReference, ctx: &Ctx, local: &LocalCtx) -> Result<MutType, Error> {
        match &mut_ref.x {
            MutReferenceX::Base(n) =>
                Ok(ctx.muts.get(n).ok_or(Error::spanned(mut_ref.span, format!("mutable `{}` not declared", n)))?.typ.clone()),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                let (mut_type, _) = typ.get_mut_type(ctx).map_err(|msg| Error::spanned(mut_ref.span, msg))?;
                Ok(mut_type)
            }
            MutReferenceX::Index(m, t) => {
                if !TermX::type_check(t, ctx, local)?.is_int() {
                    return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
                }
                match MutReferenceX::type_check(m, ctx, local)?.borrow() {
                    MutTypeX::Base(..) => Error::spanned_err(mut_ref.span, format!("indexing into base type")),
                    MutTypeX::Array(typ) => Ok(typ.clone()),
                }
            }
            MutReferenceX::Slice(m, t1, t2) => {
                if let Some(t1) = t1 {
                    if !TermX::type_check(t1, ctx, local)?.is_int() {
                        return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
                    }
                }
                if let Some(t2) = t2 {
                    if !TermX::type_check(t2, ctx, local)?.is_int() {
                        return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
                    }
                }
                let typ = MutReferenceX::type_check(m, ctx, local)?;
                match typ.borrow() {
                    MutTypeX::Base(..) => Error::spanned_err(mut_ref.span, format!("slicing into base type")),
                    MutTypeX::Array(..) => Ok(typ),
                }
            }
        }
    }

    /// Overapproximate the mutable reference as a set of mutable reference types
    pub fn approximate(mut_ref: &MutReference, ctx: &Ctx, local: &LocalCtx) -> Result<Vec<MutReferenceType>, Error> {
        match &mut_ref.x {
            MutReferenceX::Base(n) =>
                Ok(vec![Rc::new(MutReferenceTypeX::Base(n.clone()))]),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                let (_, base_refs) = typ.get_mut_type(ctx).map_err(|msg| Error::spanned(mut_ref.span, msg))?;
                Ok(base_refs)
            }
            MutReferenceX::Index(m, t) => {
                let refs = MutReferenceX::approximate(m, ctx, local)?;
                Ok(refs.iter()
                    .map(|r| Rc::new(MutReferenceTypeX::Index(r.clone(), MutReferenceIndex::from_term(t))))
                    .collect())
            }
            MutReferenceX::Slice(m, t1, t2) => {
                let refs = MutReferenceX::approximate(m, ctx, local)?;
                Ok(refs.iter()
                    .map(|r|
                        Rc::new(MutReferenceTypeX::Slice(
                            r.clone(),
                            t1.clone().map(|t| MutReferenceIndex::from_term(&t)),
                            t2.clone().map(|t| MutReferenceIndex::from_term(&t)),
                        )))
                    .collect())
            }
        }
    }

    /// Concretize a mutable reference with potentially a deref at the base
    /// (if there is no deref, the result should be identical to the original mutable reference)
    pub fn concretize(mut_ref: &MutReference, ctx: &Ctx, local: &mut LocalCtx) -> Result<Vec<MutReference>, Error> {
        match &mut_ref.x {
            MutReferenceX::Base(..) => Ok(vec![mut_ref.clone()]),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                let (_, base_refs) = typ.get_mut_type(ctx).map_err(|msg| Error::spanned(mut_ref.span, msg))?;
                Ok(base_refs.iter().map(|r| r.concretize(local)).collect())
            }
            MutReferenceX::Index(m, t) =>
                Ok(Self::concretize(m, ctx, local)?.into_iter()
                    .map(|m| Spanned::new(MutReferenceX::Index(m, t.clone()))).collect()),
            MutReferenceX::Slice(m, t1, t2) =>
                Ok(Self::concretize(m, ctx, local)?.into_iter()
                    .map(|m| Spanned::new(MutReferenceX::Slice(m, t1.clone(), t2.clone()))).collect()),
        }
    }

    // / Check that the terms are well-typed
    // / and we are not indexing into base types.
    // / 
    // / Return:
    // / 1. Type of the mutable reference (i.e. if mut A: [int], type_check(A[1]) = int)
    // / 2. Overapproximation of the base reference as MutReferenceType
    // / 3. Overapproximation of the entire reference as MutReferenceType
    // pub fn type_check(mut_ref: &MutReference, ctx: &Ctx, local: &LocalCtx) -> Result<(MutType, Vec<MutReferenceType>, Vec<MutReferenceType>), Error> {
    //     match &mut_ref.x {
    //         MutReferenceX::Base(n) =>
    //             Ok((
    //                 ctx.muts.get(n).ok_or(Error::spanned(mut_ref.span, format!("mutable `{}` not declared", n)))?.typ.clone(),
    //                 vec![Rc::new(MutReferenceTypeX::Base(n.clone()))],
    //                 vec![Rc::new(MutReferenceTypeX::Base(n.clone()))],
    //             )),
    //         MutReferenceX::Deref(t) => {
    //             let typ = TermX::type_check(t, ctx, local)?;
    //             let (mut_type, base_refs) = typ.get_mut_type(ctx).map_err(|msg| Error::spanned(mut_ref.span, msg))?;
    //             Ok((mut_type, base_refs, base_refs.clone()))
    //         }
    //         MutReferenceX::Index(m, t) => {
    //             if !TermX::type_check(t, ctx, local)?.is_int() {
    //                 return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
    //             }
    //             let (typ, base_refs, top_refs) = MutReferenceX::type_check(m, ctx, local)?;
    //             match typ.borrow() {
    //                 MutTypeX::Base(..) => Error::spanned_err(mut_ref.span, format!("indexing into base type")),
    //                 MutTypeX::Array(typ) =>
    //                     Ok((
    //                         typ.clone(),
    //                         base_refs,
    //                         // Built an extra indexing operation on top_refs
    //                         top_refs.iter()
    //                             .map(|r| Rc::new(MutReferenceTypeX::Index(r.clone(), MutReferenceIndex::from_term(t))))
    //                             .collect(),
    //                     )),
    //             }
    //         }
    //         MutReferenceX::Slice(m, t1, t2) => {
    //             if let Some(t1) = t1 {
    //                 if !TermX::type_check(t1, ctx, local)?.is_int() {
    //                     return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
    //                 }
    //             }
    //             if let Some(t2) = t2 {
    //                 if !TermX::type_check(t2, ctx, local)?.is_int() {
    //                     return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
    //                 }
    //             }
    //             let (typ, base_refs, top_refs) = MutReferenceX::type_check(m, ctx, local)?;
    //             match typ.borrow() {
    //                 MutTypeX::Base(..) => Error::spanned_err(mut_ref.span, format!("indexing into base type")),
    //                 MutTypeX::Array(..) =>
    //                     Ok((
    //                         typ,
    //                         base_refs,
    //                         // Built an extra slicing operation on top_refs
    //                         top_refs.iter()
    //                             .map(|r|
    //                                 Rc::new(MutReferenceTypeX::Slice(
    //                                     r.clone(),
    //                                     t1.map(|t| MutReferenceIndex::from_term(&t)),
    //                                     t2.map(|t| MutReferenceIndex::from_term(&t)),
    //                                 )))
    //                             .collect(),
    //                     )),
    //             }
    //         }
    //     }
    // }
}

impl TermX {
    /// Checks the type of a term under a local context
    /// Returns either the type or an error message
    pub fn type_check(term: &Term, ctx: &Ctx, local: &LocalCtx) -> Result<TermType, Error> {
        match &term.x {
            TermX::Var(var) => Ok(local
                .vars
                .get(var)
                .ok_or(Error::spanned(term.span, format!("variable `{}` not in context", var)))?
                .clone()),
            TermX::Const(c) =>
                ctx.consts
                    .get(c)
                    .map(|decl| TermTypeX::base(&decl.typ))
                    .ok_or(Error::spanned(term.span, format!("constant `{}` not defined", c))),
            TermX::Ref(m) => {
                MutReferenceX::type_check(m, ctx, local)?;
                let refs = MutReferenceX::approximate(m, ctx, local)?;
                Ok(Rc::new(TermTypeX::Ref(refs)))
            },
            TermX::Bool(_) => Ok(TermTypeX::bool()),
            TermX::Int(_) => Ok(TermTypeX::int()),
            TermX::Add(t1, t2) | TermX::Mul(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_int() {
                    Ok(TermTypeX::int())
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Less(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_int() {
                    Ok(TermTypeX::bool())
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::And(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1.is_bool() {
                    Ok(TermTypeX::bool())
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Equal(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && !typ1.is_ref() {
                    Ok(TermTypeX::bool())
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Not(t) => {
                if TermX::type_check(t, ctx, local)?.is_bool() {
                    Ok(TermTypeX::bool())
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
        }
    }
}

impl PermissionX {
    pub fn type_check(perm: &Permission, ctx: &Ctx, local: &LocalCtx) -> Result<(), Error> {
        match &perm.x {
            PermissionX::Empty => Ok(()),
            PermissionX::Add(p1, p2) =>
                PermissionX::type_check(p1, ctx, local).and(PermissionX::type_check(p2, ctx, local)),
            PermissionX::Sub(p1, p2) =>
                PermissionX::type_check(p1, ctx, local).and(PermissionX::type_check(p2, ctx, local)),
            PermissionX::Ite(t, p1, p2) => {
                if !TermX::type_check(t, ctx, local)?.is_bool() {
                    Error::spanned_err(perm.span, format!("permission if condition is not of type bool"))
                } else {
                    PermissionX::type_check(p1, ctx, local)?;
                    PermissionX::type_check(p2, ctx, local)?;
                    Ok(())
                }
            }
            // TODO: should we allow deref in permission?
            PermissionX::Fraction(_, mut_ref) => MutReferenceX::type_check(mut_ref, ctx, local).map(|_| ()),
            PermissionX::Var(v, terms) => {
                let decl = ctx.perms.get(v)
                    .ok_or(Error::spanned(perm.span, format!("permission variable `{}` not declared", v)))?;

                if decl.param_typs.len() != terms.len() {
                    return Error::spanned_err(
                        perm.span,
                        format!("unmatched number of arguments provided for permission variable `{}`: expect {}, given {}", v, decl.param_typs.len(), terms.len()),
                    );
                }

                for (typ, term) in decl.param_typs.iter().zip(terms) {
                    if !TermX::type_check(term, ctx, local)?.is_subtype(&TermTypeX::base(typ)) {
                        return Error::spanned_err(
                            perm.span,
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
    /// Updates a list of permission constraints
    /// If the type checking fails, the permission constraints might still be updated
    fn type_check_inplace(
        proc: &Proc,
        ctx: &Ctx,
        local: &mut LocalCtx,
        rctx: &mut ResourceCtx,
        mut path_conditions: Vector<Term>,
        constraints: &mut Vec<PermJudgment>,
    ) -> Result<(), Error> {
        match &proc.x {
            ProcX::Skip => Ok(()),
            ProcX::Send(c, t, k) => {
                let chan_decl = ctx
                    .chans
                    .get(c)
                    .ok_or(Error::spanned(proc.span, format!("channel `{}` does not exist", c)))?;

                let t_typ = TermX::type_check(t, ctx, local)?;
                if !t_typ.is_subtype(&chan_decl.typ) {
                    return Error::spanned_err(proc.span, format!("unmatched send channel type: expecting {}, got {}", chan_decl.typ, t_typ));
                }

                // Output resource should be in the resouce context
                if !rctx.outs.contains(c) {
                    return Error::spanned_err(proc.span, format!("resouce `output {}` not declared", c));
                }
                
                // Need to spend the permission required by the channel
                let send_perm = PermissionX::substitute_one(
                    &chan_decl.perm,
                    &chan_decl.name,
                    t,
                );
                constraints.push(PermJudgment {
                    local: local.clone(),
                    local_constraints: path_conditions.clone(),
                    perm_constraint: PermConstraintX::less_eq(&send_perm, &rctx.perm),
                });
                rctx.perm = PermissionX::sub(&rctx.perm, &send_perm);

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, path_conditions, constraints)
            }
            ProcX::Recv(c, v, k) => {
                let chan_decl = ctx
                    .chans
                    .get(c)
                    .ok_or(Error::spanned(proc.span, format!("channel `{}` does not exist", c)))?;

                // Input resource should be in the resouce context
                if !rctx.ins.contains(c) {
                    return Error::spanned_err(proc.span, format!("resouce `input {}` not declared", c));
                }

                // Receive the permission contained in the channel
                let recv_perm = PermissionX::substitute_one(
                    &chan_decl.perm,
                    &chan_decl.name,
                    &TermX::var(v),
                );
                rctx.perm = PermissionX::add(&rctx.perm, &recv_perm);

                // Receive a new variable
                if local.vars.contains_key(v) {
                    return Error::spanned_err(proc.span, format!("shadowing of local variable `{}` not supported", v));
                }
                if ctx.consts.contains_key(&Const::from(v)) {
                    return Error::spanned_err(proc.span, format!("shadowing of constant `{}` not supported", v));
                }
                local.vars.insert(v.clone(), chan_decl.typ.clone());

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, path_conditions, constraints)
            }
            ProcX::Write(m, t, k) => {
                // Check t matches the type of the reference
                let t_typ = TermX::type_check(t, ctx, local)?;

                if let MutTypeX::Base(base) = MutReferenceX::type_check(m, ctx, local)?.borrow() {
                    if !t_typ.is_subtype(&TermTypeX::base(base)) {
                        return Error::spanned_err(proc.span, format!("write type is different from mutable type: expect {}, got {}", t_typ, base));
                    }
                } else {
                    return Error::spanned_err(proc.span, format!("cannot write to a non-base-typed mutable reference"));
                }

                // Check that we have suitable write permission
                // (for all possibly referenced mutables)
                if !m.has_deref() {
                    constraints.push(PermJudgment {
                        local: local.clone(),
                        local_constraints: path_conditions.clone(),
                        perm_constraint: PermConstraintX::has_write(&m, &rctx.perm),
                    });
                } else {
                    let mut local_copy = local.clone(); // need to host the extra fresh variables for unknowns (*)
                    for concrete_ref in MutReferenceX::concretize(m, ctx, &mut local_copy)? {
                        constraints.push(PermJudgment {
                            local: local_copy.clone(),
                            local_constraints: path_conditions.clone(),
                            perm_constraint: PermConstraintX::has_write(&concrete_ref, &rctx.perm),
                        });
                    }
                }

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, path_conditions, constraints)
            }
            ProcX::Read(m, v, k) => {
                // Get the return type of the read
                let mut_typ = MutReferenceX::type_check(m, ctx, local)?;

                // Check that we have suitable read permission
                // (for all possibly referenced mutables)
                if !m.has_deref() {
                    constraints.push(PermJudgment {
                        local: local.clone(),
                        local_constraints: path_conditions.clone(),
                        perm_constraint: PermConstraintX::has_read(m, &rctx.perm),
                    });
                } else {
                    let mut local_copy = local.clone(); // need to host the extra fresh variables for unknowns (*)
                    for concrete_ref in MutReferenceX::concretize(m, ctx, &mut local_copy)? {
                        constraints.push(PermJudgment {
                            local: local_copy.clone(),
                            local_constraints: path_conditions.clone(),
                            perm_constraint: PermConstraintX::has_read(&concrete_ref, &rctx.perm),
                        });
                    }
                }

                // Update local context with new binding
                if let MutTypeX::Base(m_base) = mut_typ.borrow() {
                    // Add read variable into context
                    if local.vars.contains_key(v) {
                        return Error::spanned_err(proc.span, format!("shadowing of local variable `{}` not supported", v));
                    }
                    if ctx.consts.contains_key(&Const::from(v)) {
                        return Error::spanned_err(proc.span, format!("shadowing of constant `{}` not supported", v));
                    }
                    local.vars.insert(v.clone(), TermTypeX::base(m_base));
                } else {
                    return Error::spanned_err(proc.span, format!("cannot read from a non-base-typed mutable reference"));
                }

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, path_conditions, constraints)
            }
            ProcX::Ite(t, k1, k2) => {
                if !TermX::type_check(t, ctx, local)?.is_bool() {
                    return Error::spanned_err(proc.span, format!("if condition not of type bool"));
                }

                let mut local_copy = local.clone();
                let mut res_copy = rctx.clone();

                let mut path_conditions_copy = path_conditions.clone();

                // Push respective path conditions
                path_conditions.push_back(t.clone());
                path_conditions_copy.push_back(TermX::not(t));

                ProcX::type_check_inplace(k1, ctx, local, rctx, path_conditions, constraints)
                    .and(ProcX::type_check_inplace(k2, ctx, &mut local_copy, &mut res_copy, path_conditions_copy, constraints))
            }

            // P <args> has the same typing rules as P <args> || skip
            ProcX::Call(..) =>
                ProcX::type_check_inplace(
                    &ProcX::par(proc, &ProcX::skip()),
                    ctx, local, rctx, path_conditions, constraints,
                ),

            // TODO: currently, we only allow process calls to
            // be the LHS of a parallel composition.
            // Because the split of permissions need to be explicitly specified
            ProcX::Par(k1, k2) => {
                if let ProcX::Call(name, args) = &k1.x {
                    let proc_decl = ctx.procs.get(name)
                        .ok_or(Error::spanned(k1.span, format!("process `{}` does not exist", name)))?;

                    // Check argument types are correct
                    if args.len() != proc_decl.params.len() {
                        return Error::spanned_err(k1.span, format!("mismatched number of arguments"));
                    }

                    // Check argument types and construct param -> arg mapping
                    let mut subst = IndexMap::new();

                    for (arg, param) in args.iter().zip(&proc_decl.params) {
                        if !TermX::type_check(arg, ctx, local)?.is_subtype(&param.typ) {
                            return Error::spanned_err(k1.span, format!("unmatched argument type"));
                        }
                        subst.insert(param.name.clone(), arg.clone());
                    }

                    // Check sufficient resources are provided
                    for res in &proc_decl.res {
                        match &res.x {
                            ProcResourceX::Perm(p) => {
                                // Should have enough resource to call the process
                                let p_subst = PermissionX::substitute(p, &subst);
                                constraints.push(PermJudgment {
                                    local: local.clone(),
                                    local_constraints: path_conditions.clone(),
                                    perm_constraint: PermConstraintX::less_eq(&p_subst, &rctx.perm),
                                });
                                rctx.perm = PermissionX::sub(&rctx.perm, &p_subst);
                            },

                            // Check that input/output channels are within the resource context
                            ProcResourceX::Input(name) =>
                                if !rctx.ins.shift_remove(name) {
                                    return Error::spanned_err(k1.span, format!("required resource `input {}` not present at call site", name))
                                }

                            ProcResourceX::Output(name) =>
                                if !rctx.outs.shift_remove(name) {
                                    return Error::spanned_err(k1.span, format!("required resource `output {}` not present at call site", name))
                                }
                        }
                    }

                    // Continue checking the rest of the parallel composition
                    ProcX::type_check_inplace(k2, ctx, local, rctx, path_conditions, constraints)
                } else {
                    Error::spanned_err(proc.span, format!("currently only process calls are allowed to be the LHS of ||"))
                }
            },
            ProcX::Debug(k) => {
                println!("local context: {:?}", local);
                println!("resouce context: {:?}", rctx);
                ProcX::type_check_inplace(k, ctx, local, rctx, path_conditions, constraints)
            }
        }
    }

    pub fn type_check(proc: &Proc, ctx: &Ctx, local: &LocalCtx, rctx: &ResourceCtx) -> Result<Vec<PermJudgment>, Error> {
        let mut local_copy = local.clone();
        let mut rctx_copy = rctx.clone();
        let mut constraints = Vec::new();
        ProcX::type_check_inplace(proc, ctx, &mut local_copy, &mut rctx_copy, Vector::new(), &mut constraints)?;
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
    pub fn type_check(
        &self,
        mode: &mut PermCheckMode,
    ) -> Result<(), Error> {
        // Mutables types are base types and are always correct

        // Check mutable types are all non-reference types
        for decl in self.muts.values() {
            decl.typ.get_base_type().type_check(self).map_err(|msg| Error::spanned(decl.span, msg))?;
        }

        // Check channel types
        for decl in self.chans.values() {
            decl.typ.type_check(self).map_err(|msg| Error::spanned(decl.span, msg))?;
            PermissionX::type_check(
                &decl.perm,
                self,
                &LocalCtx {
                    vars: IndexMap::from([(Var::from(&decl.name), decl.typ.clone())]),
                },
            )?;
        }

        let mut all_constraints = Vec::new();
        let mut all_perm_valid = true;

        // Check process types
        for decl in self.procs.values() {
            let mut local = LocalCtx {
                vars: IndexMap::new(),
            };
            let mut rctx = ResourceCtx {
                perm: PermissionX::empty(),
                ins: IndexSet::new(),
                outs: IndexSet::new(),
            };

            for param in &decl.params {
                param.typ.type_check(self).map_err(|msg| Error::spanned(decl.span, msg))?;
                local.vars.insert(param.name.clone(), param.typ.clone());
            }

            for res in &decl.res {
                match &res.x {
                    ProcResourceX::Perm(perm) => {
                        PermissionX::type_check(perm, self, &local)?;
                        rctx.perm = PermissionX::add(rctx.perm, perm);
                    },
                    ProcResourceX::Input(name) => {
                        if !self.chans.contains_key(name) {
                            return Error::spanned_err(res.span, format!("channel `{}` does not exist", name));
                        }

                        if !rctx.ins.insert(name.clone()) {
                            return Error::spanned_err(res.span, format!("duplicate `input {}`", name));
                        }
                    },
                    ProcResourceX::Output(name) => {
                        if !self.chans.contains_key(name) {
                            return Error::spanned_err(res.span, format!("channel `{}` does not exist", name));
                        }

                        if !rctx.outs.insert(name.clone()) {
                            return Error::spanned_err(res.span, format!("duplicate `output {}`", name));
                        }
                    },
                }
            }

            let constraints = ProcX::type_check(&decl.body, self, &local, &rctx)?;

            println!("permission constraints for `{}`:", decl.name);
            for constraint in &constraints {
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

        if let PermCheckMode::Infer(solver, options) = mode {
            match PermJudgment::infer_perm_var(all_constraints, options, self, solver)? {
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
            Error::new_err(format!("type checking failed"))
        }
    }
}
