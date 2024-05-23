use std::fmt;
use indexmap::{IndexMap, IndexSet};

use crate::ast::*;
use crate::permission::*;
use crate::smt;
use crate::smt::EncodingCtx;
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
    pub vars: IndexMap<Var, BaseType>,
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
    pub fn is_ref(&self) -> bool {
        match self {
            BaseType::Bool => false,
            BaseType::Int => false,
            BaseType::Ref(..) => true,
        }
    }

    /// Checks if self <= other in subtyping
    pub fn is_subtype(&self, other: &BaseType) -> bool {
        match self {
            BaseType::Bool => self == other,
            BaseType::Int => self == other,
            BaseType::Ref(ns, level1) => match other {
                BaseType::Bool => false,
                BaseType::Int => false,
                BaseType::Ref(ms, level2) =>
                    // ns is included in ms
                    level1 == level2 &&
                    ns.iter().collect::<IndexSet<_>>().is_subset(&ms.iter().collect::<IndexSet<_>>()),
            },
        }
    }

    // Try to get the base type of a reference type
    pub fn get_ref_type(&self, ctx: &Ctx) -> Result<MutType, String> {
        match self {
            BaseType::Bool => Err(format!("bool cannot be deferenced")),
            BaseType::Int => Err(format!("bool cannot be deferenced")),
            BaseType::Ref(ns, level) => {
                let ref_types = ns
                    .iter()
                    .map(|n|
                        Ok::<MutType, String>(ctx.muts
                            .get(n)
                            .ok_or(format!("mutable `{}` not defined", n))?.typ.clone()
                        ))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .collect::<IndexSet<_>>();

                if ref_types.len() != 1 {
                    return Err(format!(
                        "reference to mutable(s) with inconsistent types {}",
                        ref_types.iter().map(|t| t.to_string()).collect::<String>(),
                    ));
                }

                let mut_type = ref_types.first().unwrap();
                MutTypeX::get_deref_type(mut_type, *level)
                    .ok_or(format!("mutable type {} cannot be dereferenced {} time(s)", mut_type, level))
            }
        }
    }

    /// Type check the reference type
    pub fn type_check(&self, ctx: &Ctx) -> Result<(), String> {
        match self {
            BaseType::Bool => Ok(()),
            BaseType::Int => Ok(()),
            BaseType::Ref(..) => self.get_ref_type(ctx).map(|_| ()),
        }
    }
}

impl MutReferenceX {
    /// Check that the terms are well-typed
    /// and we are not indexing into base types.
    /// Return the type of the mutable reference
    /// and all global mutables that are potentially
    /// referenced.
    /// type_check(ref) = (type, referenced mutables, number of times dereferenced)
    /// e.g. if mut A: [[int]], then
    /// type_check(A[1]) = [int], {A}, 1
    /// type_check(A[1:]) = [[int]], {A}, 0
    /// type_check(A[1][2]) = int, {A}, 2
    /// type_check(*x[1][2]) = int, {A, B}, 2 (if x: &{A, B})
    pub fn type_check(mut_ref: &MutReference, ctx: &Ctx, local: &LocalCtx) -> Result<(MutType, IndexSet<MutName>, usize), Error> {
        match &mut_ref.x {
            MutReferenceX::Base(n) =>
                Ok((
                    ctx.muts.get(n).ok_or(Error::spanned(mut_ref.span, format!("mutable `{}` not declared", n)))?.typ.clone(),
                    IndexSet::from([n.clone()]),
                    0,
                )),
            MutReferenceX::Deref(t) => {
                let typ = TermX::type_check(t, ctx, local)?;
                match &typ {
                    BaseType::Bool => Error::spanned_err(mut_ref.span, format!("dereferencing bool")),
                    BaseType::Int => Error::spanned_err(mut_ref.span, format!("dereferencing int")),
                    BaseType::Ref(names, level) => Ok((
                        typ.get_ref_type(ctx).map_err(|msg| Error::spanned(mut_ref.span, msg))?,
                        names.iter().map(|n| n.clone()).collect(),
                        *level,
                    )),
                }
            }
            MutReferenceX::Index(m, t) => {
                if TermX::type_check(t, ctx, local)? != BaseType::Int {
                    return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
                }
                let (typ, names, level) = MutReferenceX::type_check(m, ctx, local)?;
                match typ.as_ref() {
                    MutTypeX::Base(..) => Error::spanned_err(mut_ref.span, format!("indexing into base type")),
                    MutTypeX::Array(t) => Ok((t.clone(), names, level + 1)),
                }
            }
            MutReferenceX::Slice(m, t1, t2) => {
                if let Some(t1) = t1 {
                    if TermX::type_check(t1, ctx, local)? != BaseType::Int {
                        return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
                    }
                }
                if let Some(t2) = t2 {
                    if TermX::type_check(t2, ctx, local)? != BaseType::Int {
                        return Error::spanned_err(mut_ref.span, format!("index to a mutable should be int"));
                    }
                }
                let (typ, names, level) = MutReferenceX::type_check(m, ctx, local)?;
                match typ.as_ref() {
                    MutTypeX::Base(..) => Error::spanned_err(mut_ref.span, format!("indexing into base type")),
                    MutTypeX::Array(..) => Ok((typ, names, level)),
                }
            }
        }
    }
}

impl TermX {
    /// Checks the type of a term under a local context
    /// Returns either the type or an error message
    pub fn type_check(term: &Term, ctx: &Ctx, local: &LocalCtx) -> Result<BaseType, Error> {
        match &term.x {
            TermX::Var(var) => Ok(local
                .vars
                .get(var)
                .ok_or(Error::spanned(term.span, format!("variable `{}` not in context", var)))?
                .clone()),
            TermX::Const(c) =>
                ctx.consts
                    .get(c)
                    .map(|decl| decl.typ.clone())
                    .ok_or(Error::spanned(term.span, format!("constant `{}` not defined", c))),
            TermX::Ref(m) => {
                let (_, names, level) = MutReferenceX::type_check(m, ctx, local)?;
                // match m_typ.as_ref() {
                //     // TODO: check this
                //     MutTypeX::Base(..) => Ok(BaseType::Ref(names.iter().map(|n| n.clone()).collect::<Vec<_>>()[..].into())),
                //     MutTypeX::Array(..) => Err(format!("non-first level reference currently not supported")),
                // }
                // TODO: use m_typ
                Ok(BaseType::Ref(names.iter().map(|n| n.clone()).collect::<Vec<_>>()[..].into(), level))
            },
            TermX::Bool(_) => Ok(BaseType::Bool),
            TermX::Int(_) => Ok(BaseType::Int),
            TermX::Add(t1, t2) | TermX::Mul(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1 == BaseType::Int {
                    Ok(BaseType::Int)
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Less(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1 == BaseType::Int {
                    Ok(BaseType::Bool)
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::And(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && typ1 == BaseType::Bool {
                    Ok(BaseType::Bool)
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Equal(t1, t2) => {
                let typ1 = TermX::type_check(t1, ctx, local)?;
                let typ2 = TermX::type_check(t2, ctx, local)?;
                if typ1 == typ2 && !typ1.is_ref() {
                    Ok(BaseType::Bool)
                } else {
                    Error::spanned_err(term.span, format!("incorrect subterm type"))
                }
            }
            TermX::Not(t) => {
                if TermX::type_check(t, ctx, local)? == BaseType::Bool {
                    Ok(BaseType::Bool)
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
                if TermX::type_check(t, ctx, local)? != BaseType::Bool {
                    Error::spanned_err(perm.span, format!("permission if condition is not of type bool"))
                } else {
                    PermissionX::type_check(p1, ctx, local)?;
                    PermissionX::type_check(p2, ctx, local)?;
                    Ok(())
                }
            }
            // TODO: should we allow deref in permission?
            PermissionX::Fraction(_, mut_ref) => MutReferenceX::type_check(mut_ref, ctx, local).map(|_| ()),
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
        constraints: &mut Vec<(PermConstraint, LocalCtx)>,
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
                    &Var::from(&chan_decl.name),
                    t,
                );
                constraints.push((PermConstraintX::less_eq(&send_perm, &rctx.perm), local.clone()));
                rctx.perm = PermissionX::sub(&rctx.perm, &send_perm);

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, constraints)
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
                    &Var::from(&chan_decl.name),
                    &TermX::var(&v),
                );
                rctx.perm = PermissionX::add(&rctx.perm, &recv_perm);

                // Receive a new variable
                local.vars.insert(v.clone(), chan_decl.typ.clone());

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, constraints)
            }
            ProcX::Write(m, t, k) => {
                // Check t matches the type of the reference
                let t_typ = TermX::type_check(t, ctx, local)?;

                let (m_typ, m_names, _) = MutReferenceX::type_check(m, ctx, local)?;
                if let MutTypeX::Base(m_base) = m_typ.as_ref() {
                    if t_typ != *m_base {
                        return Error::spanned_err(proc.span, format!("write type is different from mutable type"));
                    }
                } else {
                    return Error::spanned_err(proc.span, format!("cannot write to a non-base-typed mutable reference"));
                }

                // Check that we have suitable write permission
                // (for all possibly referenced mutables)
                // TODO: simplify m
                if m.is_simple() {
                    constraints.push((PermConstraintX::has_write(m, &rctx.perm), local.clone()));
                } else {
                    for m_name in &m_names {
                        constraints.push((PermConstraintX::has_write(
                            &Spanned::new(MutReferenceX::Base(m_name.clone())),
                            // &MutReferenceX::substitute_deref_with_mut_name(m, m_name),
                            &rctx.perm,
                        ), local.clone()));
                    }
                }

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, constraints)
            }
            ProcX::Read(m, v, k) => {
                // Get the return type of the read
                let (m_typ, m_names, _) = MutReferenceX::type_check(m, ctx, local)?;

                // Check that we have suitable read permission
                // (for all possibly referenced mutables)
                // TODO: simplify m
                if m.is_simple() {
                    constraints.push((PermConstraintX::has_read(m, &rctx.perm), local.clone()));
                } else {
                    // Overapproximate and require the permission of the entire mutable
                    for m_name in &m_names {
                        constraints.push((PermConstraintX::has_read(
                            &Spanned::new(MutReferenceX::Base(m_name.clone())),
                            // &MutReferenceX::substitute_deref_with_mut_name(m, m_name),
                            &rctx.perm,
                        ), local.clone()));
                    }
                }

                // Update local context with new binding
                if let MutTypeX::Base(m_base) = m_typ.as_ref() {
                    // Add read variable into context
                    local.vars.insert(v.clone(), m_base.clone());
                } else {
                    return Error::spanned_err(proc.span, format!("cannot read from a non-base-typed mutable reference"));
                }

                // Check rest of the process
                ProcX::type_check_inplace(k, ctx, local, rctx, constraints)
            }
            ProcX::Ite(t, k1, k2) => {
                if TermX::type_check(t, ctx, local)? != BaseType::Bool {
                    return Error::spanned_err(proc.span, format!("if condition not of type bool"));
                }

                let mut local_copy = local.clone();
                let mut res_copy = rctx.clone();

                ProcX::type_check_inplace(k1, ctx, local, rctx, constraints)
                    .and(ProcX::type_check_inplace(k2, ctx, &mut local_copy, &mut res_copy, constraints))
            }

            // P <args> has the same typing rules as P <args> || skip
            ProcX::Call(..) =>
                ProcX::type_check_inplace(&ProcX::par(proc, &ProcX::skip()), ctx, local, rctx, constraints),

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
                                constraints.push((PermConstraintX::less_eq(&p_subst, &rctx.perm), local.clone()));
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
                    ProcX::type_check_inplace(k2, ctx, local, rctx, constraints)
                } else {
                    Error::spanned_err(proc.span, format!("currently only process calls are allowed to be the LHS of ||"))
                }
            },
            ProcX::Debug(k) => {
                println!("local context: {:?}", local);
                println!("resouce context: {:?}", rctx);
                ProcX::type_check_inplace(k, ctx, local, rctx, constraints)
            }
        }
    }

    pub fn type_check(proc: &Proc, ctx: &Ctx, local: &LocalCtx, rctx: &ResourceCtx) -> Result<Vec<(PermConstraint, LocalCtx)>, Error> {
        let mut local_copy = local.clone();
        let mut rctx_copy = rctx.clone();
        let mut constraints = Vec::new();
        ProcX::type_check_inplace(proc, ctx, &mut local_copy, &mut rctx_copy, &mut constraints)?;
        Ok(constraints)
    }
}

impl Ctx {
    /// Type-check everything in a context
    pub fn type_check(&self, solver: &mut smt::Solver) -> Result<(), Error> {
        // Mutables types are base types and are always correct

        // Check mutable types are all non-reference types
        for decl in self.muts.values() {
            let base = decl.typ.get_base_type();
            match base {
                BaseType::Bool => Ok(()),
                BaseType::Int => Ok(()),
                BaseType::Ref(..) => Error::spanned_err(decl.span, format!("mutable `{}` cannot have a reference type", decl.name)),
            }?
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
                        rctx.perm = PermissionX::add(&rctx.perm, &perm);
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

            // TODO: better error handling
            let mut smt_constraints = Vec::new();
            let mut smt_ctx = EncodingCtx::new("perm");
            let constraints = ProcX::type_check(&decl.body, self, &local, &rctx)?;

            solver.push().expect("failed to push");

            println!("checking permissions for `{}`:", decl.name);
            // Convert permission constraints to SMT constraints
            for (constraint, local) in &constraints {
                smt_constraints.push(constraint.encode_invalidity(&mut smt_ctx, self, local, 5).unwrap());
            }

            // Send context commands
            for cmd in smt_ctx.to_commands() {
                solver.send_command(cmd).expect("failed to send command");
            }

            // Send assertions and check for validity
            for (smt_constraint, (constraint, local)) in smt_constraints.iter().zip(constraints.iter()) {
                solver.assert(smt_constraint).expect("failed to assert");

                match solver.check_sat().unwrap() {
                    smt::SatResult::Sat => {
                        let result = solver.send_command_with_output(smt::CommandX::get_model()).expect("failed to send command");
                        println!("  not valid: {} |= {}", local, constraint);
                        println!("  encoding: {}", smt_constraint);
                        print!("  model: {}", result);
                        break;
                    }
                    smt::SatResult::Unsat => {
                        println!("  valid: {} |= {}", local, constraint);
                    }
                    smt::SatResult::Unknown => {
                        println!("  unknown: {} |= {}", local, constraint);
                        break;
                    }
                }
            }

            solver.pop().expect("failed to pop");
        }

        Ok(())
    }
}
