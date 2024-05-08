use indexmap::{IndexMap, IndexSet};

use crate::ast::*;
use crate::permission::*;

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

impl TermX {
    /// Checks the type of a term under a local context
    /// Returns either the type or an error message
    pub fn type_check(&self, local: &LocalCtx) -> Result<BaseType, String> {
        match self {
            TermX::Var(var) => Ok(local
                .vars
                .get(var)
                .ok_or(format!("variable `{}` not in context", var))?
                .clone()),
            TermX::Bool(_) => Ok(BaseType::Bool),
            TermX::Int(_) => Ok(BaseType::Int),
            TermX::Add(t1, t2) | TermX::Mul(t1, t2) | TermX::Less(t1, t2) => {
                let typ1 = t1.type_check(local)?;
                let typ2 = t2.type_check(local)?;
                if typ1 == typ2 && typ1 == BaseType::Int {
                    Ok(BaseType::Int)
                } else {
                    Err(format!("incorrect subterm type"))
                }
            }
            TermX::And(t1, t2) => {
                let typ1 = t1.type_check(local)?;
                let typ2 = t2.type_check(local)?;
                if typ1 == typ2 && typ1 == BaseType::Bool {
                    Ok(BaseType::Bool)
                } else {
                    Err(format!("incorrect subterm type"))
                }
            }
            TermX::Equal(t1, t2) => {
                if t1.type_check(local)? == t2.type_check(local)? {
                    Ok(BaseType::Bool)
                } else {
                    Err(format!("incorrect subterm type"))
                }
            }
            TermX::Not(t) => {
                if t.type_check(local)? == BaseType::Bool {
                    Ok(BaseType::Bool)
                } else {
                    Err(format!("incorrect subterm type"))
                }
            }
        }
    }
}

impl PermissionX {
    pub fn type_check(&self, ctx: &Ctx, local: &LocalCtx) -> Result<(), String> {
        match self {
            PermissionX::Empty => Ok(()),
            PermissionX::Add(p1, p2) =>
                p1.type_check(ctx, local).and(p2.type_check(ctx, local)),
            PermissionX::Sub(p1, p2) =>
                p1.type_check(ctx, local).and(p2.type_check(ctx, local)),
            PermissionX::Ite(t, p1, p2) => {
                if t.type_check(local)? != BaseType::Bool {
                    Err(format!("permission if condition is not of type bool"))
                } else {
                    p1.type_check(ctx, local)?;
                    p2.type_check(ctx, local)?;
                    Ok(())
                }
            }
            PermissionX::Fraction(_, mut_ref) => match mut_ref.as_ref() {
                MutReferenceX::Base(name) => {
                    ctx.muts
                        .get(name)
                        .ok_or(format!("mutable `{}` not declared", name))?;
                    Ok(())
                }
                MutReferenceX::Index(name, t) => {
                    ctx.muts
                        .get(name)
                        .ok_or(format!("mutable `{}` not declared", name))?;
                    if t.type_check(local)? == BaseType::Int {
                        Ok(())
                    } else {
                        Err(format!("index to a mutable should be int"))
                    }
                }
                MutReferenceX::Slice(name, t1, t2) => {
                    ctx.muts
                        .get(name)
                        .ok_or(format!("mutable `{}` not declared", name))?;
                    if let Some(t1) = t1 {
                        if t1.type_check(local)? != BaseType::Int {
                            return Err(format!("index to a mutable should be int"));
                        }
                    }
                    if let Some(t2) = t2 {
                        if t2.type_check(local)? != BaseType::Int {
                            return Err(format!("index to a mutable should be int"));
                        }
                    }
                    Ok(())
                }
            },
        }
    }
}

impl ProcX {
    /// Updates a list of permission constraints
    /// If the type checking fails, the permission constraints might still be updated
    fn type_check_inplace(
        &self,
        ctx: &Ctx,
        local: &mut LocalCtx,
        rctx: &mut ResourceCtx,
        constraints: &mut Vec<PermConstraint>,
    ) -> Result<(), String> {
        match self {
            ProcX::Skip => Ok(()),
            ProcX::Send(c, t, k) => {
                let chan_decl = ctx
                    .chans
                    .get(c)
                    .ok_or(format!("channel `{}` does not exist", c))?;

                if t.type_check(local)? != chan_decl.typ {
                    return Err(format!("unmatched send channel type"));
                }

                // Output resource should be in the resouce context
                if !rctx.outs.contains(c) {
                    return Err(format!("resouce `output {}` not declared", c));
                }
                
                // Need to spend the permission required by the channel
                let send_perm = PermissionX::substitute_one(
                    &chan_decl.perm,
                    &Var::from(&chan_decl.name),
                    t,
                );
                constraints.push(PermConstraintX::less_eq(&send_perm, &rctx.perm));
                rctx.perm = PermissionX::sub(&rctx.perm, &send_perm);

                // Check rest of the process
                k.type_check_inplace(ctx, local, rctx, constraints)
            }
            ProcX::Recv(c, v, k) => {
                let chan_decl = ctx
                    .chans
                    .get(c)
                    .ok_or(format!("channel `{}` does not exist", c))?;

                // Input resource should be in the resouce context
                if !rctx.ins.contains(c) {
                    return Err(format!("resouce `input {}` not declared", c));
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
                k.type_check_inplace(ctx, local, rctx, constraints)
            }
            ProcX::Write(m, t, k) => {
                // Check t matches the type of the reference
                let t_typ = t.type_check(local)?;
                match m.as_ref() {
                    MutReferenceX::Base(name) => {
                        let mut_decl = ctx.muts.get(name).ok_or(format!("mutable `{}` does not exist", name))?;

                        match &mut_decl.typ {
                            MutType::Base(typ) => if t_typ != *typ {
                                return Err(format!("unmatched write type: writing term of type `{}` to a mutable of type `{}`", t_typ, typ));
                            }
                            MutType::Array(_) => return Err(format!("cannot write to an array type directly")),
                        }
                    }
                    MutReferenceX::Index(name, _) => {
                        let mut_decl = ctx.muts.get(name).ok_or(format!("mutable `{}` does not exist", name))?;

                        match &mut_decl.typ {
                            MutType::Base(..) => return Err(format!("indexing into a non-array mutable")),
                            MutType::Array(typ) => if t_typ != *typ {
                                return Err(format!("unmatched write type: writing term of type `{}` to an index of a mutable of type `{}`", t_typ, mut_decl.typ));
                            }
                        }
                    }
                    MutReferenceX::Slice(..) => return Err(format!("cannot write to a slice")),
                }

                // Check that we have suitable write permission
                constraints.push(PermConstraintX::has_write(&m, &rctx.perm));

                // Check rest of the process
                k.type_check_inplace(ctx, local, rctx, constraints)
            }
            ProcX::Read(m, v, k) => {
                // Get the return type of the read
                let typ = match m.as_ref() {
                    MutReferenceX::Base(name) => {
                        let mut_decl = ctx.muts.get(name).ok_or(format!("mutable `{}` does not exist", name))?;

                        match &mut_decl.typ {
                            MutType::Base(typ) => typ,
                            MutType::Array(_) => return Err(format!("cannot read from an array mutable directly")),
                        }
                    }
                    MutReferenceX::Index(name, _) => {
                        let mut_decl = ctx.muts.get(name).ok_or(format!("mutable `{}` does not exist", name))?;

                        match &mut_decl.typ {
                            MutType::Base(..) => return Err(format!("indexing into a non-array mutable")),
                            MutType::Array(typ) => typ,
                        }
                    }
                    MutReferenceX::Slice(..) => return Err(format!("cannot write to a slice")),
                };

                // Check that we have suitable read permission
                constraints.push(PermConstraintX::has_read(&m, &rctx.perm));

                // Add read variable into context
                local.vars.insert(v.clone(), typ.clone());

                // Check rest of the process
                k.type_check_inplace(ctx, local, rctx, constraints)
            }
            ProcX::Ite(t, k1, k2) => {
                if t.type_check(local)? != BaseType::Bool {
                    return Err(format!("if condition not of type bool"));
                }

                let mut local_copy = local.clone();
                let mut res_copy = rctx.clone();

                k1.type_check_inplace(ctx, local, rctx, constraints)
                    .and(k2.type_check_inplace(ctx, &mut local_copy, &mut res_copy, constraints))
            }

            // P <args> has the same typing rules as P <args> || skip
            ProcX::Call(name, args) =>
                ProcX::par(&ProcX::call(&name, args), &ProcX::skip())
                    .type_check_inplace(ctx, local, rctx, constraints),

            // TODO: currently, we only allow process calls to
            // be the LHS of a parallel composition.
            // Because the split of permissions need to be explicitly specified
            ProcX::Par(k1, k2) => {
                if let ProcX::Call(name, args) = k1.as_ref() {
                    let proc_decl = ctx.procs.get(name).ok_or(format!("process `{}` does not exist", name))?;

                    // Check argument types are correct
                    if args.len() != proc_decl.params.len() {
                        return Err(format!("mismatched number of arguments"));
                    }

                    // Check argument types and construct param -> arg mapping
                    let mut subst = IndexMap::new();

                    for (arg, param) in args.iter().zip(&proc_decl.params) {
                        if arg.type_check(local)? != param.typ {
                            return Err(format!("unmatched argument type"));
                        }
                        subst.insert(param.name.clone(), arg.clone());
                    }

                    // Check sufficient resources are provided
                    for res in &proc_decl.res {
                        match res.as_ref() {
                            ProcResourceX::Perm(p) => {
                                // Should have enough resource to call the process
                                let p_subst = PermissionX::substitute(p, &subst);
                                constraints.push(PermConstraintX::less_eq(&p_subst, &rctx.perm));
                                rctx.perm = PermissionX::sub(&rctx.perm, &p_subst);
                            },

                            // Check that input/output channels are within the resource context
                            ProcResourceX::Input(name) =>
                                if !rctx.ins.shift_remove(name) {
                                    return Err(format!("required resource `input {}` not present at call site", name))
                                }

                            ProcResourceX::Output(name) =>
                                if !rctx.outs.shift_remove(name) {
                                    return Err(format!("required resource `output {}` not present at call site", name))
                                }
                        }
                    }

                    // Continue checking the rest of the parallel composition
                    k2.type_check_inplace(ctx, local, rctx, constraints)
                } else {
                    Err(format!("currently only process calls are allowed to be the LHS of ||"))
                }
            },
            ProcX::Debug(k) => {
                println!("local context: {:?}", local);
                println!("resouce context: {:?}", rctx);
                k.type_check_inplace(ctx, local, rctx, constraints)
            }
        }
    }

    pub fn type_check(&self, ctx: &Ctx, local: &LocalCtx, rctx: &ResourceCtx) -> Result<Vec<PermConstraint>, String> {
        let mut local_copy = local.clone();
        let mut rctx_copy = rctx.clone();
        let mut constraints = Vec::new();
        self.type_check_inplace(ctx, &mut local_copy, &mut rctx_copy, &mut constraints)?;
        Ok(constraints)
    }
}

impl Ctx {
    /// Type-check everything in a context
    pub fn type_check(&self) -> Result<(), String> {
        // Mutables types are base types and are always correct

        // Check channel types
        for decl in self.chans.values() {
            decl.perm.type_check(
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
                local.vars.insert(param.name.clone(), param.typ.clone());
            }

            for res in &decl.res {
                match res.as_ref() {
                    ProcResourceX::Perm(perm) => {
                        perm.type_check(self, &local)?;
                        rctx.perm = PermissionX::add(&rctx.perm, &perm);
                    },
                    ProcResourceX::Input(name) => {
                        if !rctx.ins.insert(name.clone()) {
                            return Err(format!("duplicate `input {}`", name));
                        }
                    },
                    ProcResourceX::Output(name) => {
                        if !rctx.outs.insert(name.clone()) {
                            return Err(format!("duplicate `output {}`", name));
                        }
                    },
                }
            }

            let constraints = decl.body.type_check(self, &local, &rctx)?;

            println!("permission constraints for process `{}`:", decl.name);
            for constraint in constraints {
                println!("  {}", constraint);
            }
        }

        Ok(())
    }
}
