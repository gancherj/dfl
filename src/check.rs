use std::rc::Rc;

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

#[derive(Clone)]
pub struct LocalCtx {
    pub vars: IndexMap<Var, BaseType>,
}

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
            PermissionX::Fraction(_, mut_ref) => match mut_ref {
                MutReference::Base(name) => {
                    ctx.muts
                        .get(name)
                        .ok_or(format!("mutable `{}` not declared", name))?;
                    Ok(())
                }
                MutReference::Index(name, t) => {
                    ctx.muts
                        .get(name)
                        .ok_or(format!("mutable `{}` not declared", name))?;
                    if t.type_check(local)? == BaseType::Int {
                        Ok(())
                    } else {
                        Err(format!("index to a mutable should be int"))
                    }
                }
                MutReference::Slice(name, t1, t2) => {
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
    pub fn type_check_inplace(
        &self,
        ctx: &Ctx,
        local: &mut LocalCtx,
        res: &mut ResourceCtx,
        constraints: &mut Vec<PermConstraint>,
    ) -> Result<(), String> {
        match self {
            ProcX::Skip => Ok(()),
            ProcX::Send(c, t, k) => {
                t.type_check(local)?;

                let chan_decl = ctx
                    .chans
                    .get(c)
                    .ok_or(format!("channel `{}` does not exist", c))?;

                // Need to spend the permission required by the channel
                let send_perm = PermissionX::substitute_one(
                    &chan_decl.perm,
                    &Var::from(&chan_decl.name),
                    t,
                );
                constraints.push(Rc::new(PermConstraintX::LessEq(send_perm.clone(), res.perm.clone())));
                res.perm = Rc::new(PermissionX::Sub(res.perm.clone(), send_perm));

                // Check rest of the process
                k.type_check_inplace(ctx, local, res, constraints)
            }
            ProcX::Recv(c, v, k) => {
                let chan_decl = ctx
                    .chans
                    .get(c)
                    .ok_or(format!("channel `{}` does not exist", c))?;

                // Receive the permission contained in the channel
                let recv_perm = PermissionX::substitute_one(
                    &chan_decl.perm,
                    &Var::from(&chan_decl.name),
                    &Rc::new(TermX::Var(v.clone())),
                );
                res.perm = Rc::new(PermissionX::Add(res.perm.clone(), recv_perm));

                // Receive a new variable
                local.vars.insert(v.clone(), chan_decl.typ.clone());

                // Check rest of the process
                k.type_check_inplace(ctx, local, res, constraints)
            }
            ProcX::Write(_, _, _) => todo!(),
            ProcX::Read(_, _, _) => todo!(),
            ProcX::Ite(_, _, _) => todo!(),
            ProcX::Call(_, _) => todo!(),
            ProcX::Par(_, _) => todo!(),
            ProcX::Debug(_) => Ok(()),
        }
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
        // for decl in self.procs.values() {

        // }

        Ok(())
    }
}
