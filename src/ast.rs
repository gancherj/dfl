use std::rc::Rc;
use std::collections::HashSet;
use std::collections::HashMap;
use fraction::Fraction;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Var {
    pvar : String,
    ident : u32
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct Chan(String);

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
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

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Permission (HashMap<Location, Fraction>);

impl Permission {
    fn empty() -> Permission {
        Permission(HashMap::new())
    }

    fn is_empty(&self) -> bool {
        let mut b = true;
        for (l, f) in &self.0 {
            if *f > Fraction::new(0u64, 1u64) {
                b = false;
            }
        }
        b
    }

    fn singleton(l : &Location, f : Option<Fraction>) -> Permission {
        Permission(HashMap::from([(l.clone(), f.unwrap_or(Fraction::new(1u64, 1u64)))]))
    }

    fn contains_write(&self, l : &Location) -> bool {
        match self.0.get(l) {
            None => false,
            Some(f) => *f >= Fraction::new(1u64, 1u64)
        }
    }

    fn contains_read(&self, l : &Location) -> bool {
        match self.0.get(l) {
            None => false,
            Some(f) => *f > Fraction::new(0u64, 1u64)
        }
    }
}


#[derive(Clone, PartialEq)]
pub struct ProcTy {
    ins : HashSet<Chan>,
    outs : HashSet<Chan>
}

impl ProcTy {
    fn sub_ty(&self, other : &ProcTy) -> bool {
        self == other
    }

    fn union(&self, other : &ProcTy) -> ProcTy {
        let mut ins = self.ins.clone();
        for x in &other.ins {
            ins.insert(x.clone());
        }
        let mut outs = self.ins.clone();
        for x in &other.outs {
            outs.insert(x.clone());
        }
        ProcTy { ins:ins, outs:outs }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct ChanTy(Permission);


#[derive(Clone)]
pub struct Ctx {
    chan_tys : HashMap<Chan, ChanTy>,
    proc_tys : HashMap<ProcName, ProcTy>,
    var_tys : HashMap<Var, ()>,
    perm : Permission
}

impl Ctx {
    fn new(chan_tys : HashMap<Chan, ChanTy>, proc_tys : HashMap<ProcName, ProcTy>) -> Ctx {
        Ctx { 
            chan_tys : chan_tys,
            proc_tys : proc_tys,
            var_tys : HashMap::new(),
            perm : Permission::empty()
        }
    }


    fn add_var(&self, x : &Var) -> Ctx {
        let mut ctx2 = self.clone();
        ctx2.var_tys.insert(x.clone(), ());
        ctx2
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
    // TODO: this should infer a type, not check against one
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
                if e.check(ctx) && ctx.perm.contains_write(loc) { 
                    k.check(ctx, t)
                }
                else { false }
            },
            Proc::PRead (loc, x, k) => {
                if ctx.perm.contains_read(loc) {
                    k.check(&ctx.add_var(&x), t)
                }
                else { false }
            },
            Proc::PCall(f) => {
                match ctx.proc_tys.get(f) {
                    None => false,
                    Some(t2) => t.sub_ty(t2)
                }
            },
            Proc::PSkip => true,
            Proc::Par(p1, p2) => {
                if !ctx.perm.is_empty() || !ctx.var_tys.is_empty() {
                    false  // Only allow top-level splits
                }
                else {
                    false // TODO: split up t
                }
            }
        }
    }
}


