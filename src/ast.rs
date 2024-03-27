use std::rc::Rc;
use std::collections::HashSet;
use std::collections::HashMap;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Var {
    pvar : String,
    ident : u32
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Chan(String);

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct Location(String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct ProcName(String);

pub enum Expr {
    EVar (Var),
    EInt (u32),
    EAdd (Rc<Expr>, Rc<Expr>)
}

pub enum Proc {
    PSend (Chan, Expr, Rc<Proc>),
    PRecv (Chan, Var, Rc<Proc>),
    PWrite (Location, Expr, Rc<Proc>),
    PRead (Location, Var, Rc<Proc>),
    PCall (ProcName),
    Par (Rc<Proc>, Rc<Proc>),
    PSkip
}

#[derive(Clone)]
pub struct ProcTy {
    ins : HashSet<Chan>,
    outs : HashSet<Chan>
}

impl ProcTy {
    fn sub_ty(&self, other : &ProcTy) -> bool {
        false // TODO
    }
}

pub struct Ctx {
    proc_tys : HashMap<ProcName, ProcTy>,
    var_tys : HashMap<Var, ()>
}

impl Ctx {
    fn add_var(&self, x : &Var) -> Ctx {
        let mut var_tys = self.var_tys.clone();
        var_tys.insert(x.clone(), ());
        Ctx {proc_tys : self.proc_tys.clone(), var_tys: var_tys}
    }
}

impl Expr {
    fn check(&self, ctx : &Ctx) -> bool {
        match self {
            Expr::EVar(x) => ctx.var_tys.get(&x).is_some(),
            Expr::EInt(_) => true,
            Expr::EAdd(e1, e2) => e1.check(ctx) && e2.check(ctx)
        }
    }
}

impl Proc {
    fn check(&self, ctx : &Ctx, t : &ProcTy) -> bool {
        match self {
            Proc::PSend (c, e, k) => {
                if t.outs.contains(c) && e.check(ctx) {
                    k.check(ctx, t)
                }
                else { false }
            },
            Proc::PRecv (c, x, k) => {
                if t.ins.contains(c) {
                    k.check(&ctx.add_var(&x), t)
                }
                else { false }
            },
            Proc::PWrite (loc, e, k) => {
                if e.check(ctx) { // TODO: permission checking goes here
                    k.check(ctx, t)
                }
                else { false }
            },
            Proc::PRead (loc, x, k) => {
                k.check(&ctx.add_var(&x), t)
            },
            Proc::PCall(f) => {
                match ctx.proc_tys.get(f) {
                    None => false,
                    Some(t2) => t.sub_ty(t2)
                }
            },
            Proc::PSkip => true,
            Proc::Par(p1, p2) => false // TODO: split up permissions, etc
        }
    }
}


