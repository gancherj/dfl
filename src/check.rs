# ![allow(unused_imports)]
#![allow(dead_code)]
use crate::ast::*;
use crate::permissions::*;
use fraction::{Fraction, One, Zero};
use im::hashmap::*;
use im::hashset::*;
use std::rc::Rc;
use std::option::*;


impl ProcTy {
    fn sub_ty(&self, other: &ProcTy) -> bool {
        self == other
    }

    fn with_input(&self, c: &Chan) -> ProcTy {
        ProcTy {
            ins: self.ins.update(c.clone()),
            outs: self.outs.clone(),
        }
    }

    fn with_output(&self, c: &Chan) -> ProcTy {
        ProcTy {
            outs: self.outs.update(c.clone()),
            ins: self.ins.clone(),
        }
    }

    fn empty() -> ProcTy {
        ProcTy {
            ins: HashSet::new(),
            outs: HashSet::new(),
        }
    }

    fn try_add(&self, other: &ProcTy) -> Result<ProcTy, String> {
        if self.ins.clone().intersection(other.ins.clone()).is_empty()
            && self.outs.clone().intersection(other.outs.clone()).is_empty()
        {
            Ok(ProcTy {
                ins: self.ins.clone().union(other.ins.clone()),
                outs: self.outs.clone().union(other.outs.clone()),
            })
        } else {
            Err("try_add".to_string())
        }
    }

    fn check(&self, ctx : &Ctx) -> bool {
        let mut ok = true;
        for c in &self.ins {
            if !ctx.chan_tys.contains_key(&c) {
                ok = false;
            }
        }
        for c in &self.outs {
            if !ctx.chan_tys.contains_key(&c) {
                ok = false;
            }
        }
        ok
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct ChanTy(Permission);

#[derive(Clone, Debug)]
pub struct Ctx {
    pub locations: HashMap<Location, ()>,
    chan_tys: HashMap<Chan, ChanTy>,
    proc_tys: HashMap<ProcName, ProcTy>,
    var_tys: HashMap<Var, ()>,
    perm: Permission,
}

impl Ctx {
    fn new() -> Ctx {
        Ctx {
            locations : HashMap::new(),
            chan_tys: HashMap::new(),
            proc_tys: HashMap::new(),
            var_tys: HashMap::new(),
            perm: Permission::empty(),
        }
    }

    fn sub_perm(&self, other: &Permission) -> Result<Ctx, String> {
        match self.perm.subtract(other) {
            Err(e) => Err(e),
            Ok(p) => Ok(Ctx {
                perm: p,
                ..self.clone()
            }),
        }
    }

    fn extend_var(&self, x: &Var) -> Ctx {
        Ctx {
            var_tys: self.var_tys.update(x.clone(), ()),
            ..self.clone()
        }
    }

    fn extend_perm(&self, p : &Permission) -> Ctx {
        Ctx {
            perm : self.perm.clone().add(p),
            ..self.clone()
        }
    }

    fn retract_perm(&self, p : &Permission) -> Result<Ctx, String> {
        self.perm.clone().subtract(p).and_then(|p2| 
            Ok(Ctx{perm:p2, ..self.clone()})
            )
    }
}

impl Expr {
    fn check(&self, ctx: &Ctx) -> bool {
        match self {
            Expr::EVar(x) => ctx.var_tys.get(&x).is_some(),
            Expr::EInt(_) => true,
            Expr::EAdd(e1, e2) => e1.check(ctx) && e2.check(ctx),
        }
    }
}

impl Proc {
    fn check(&self, ctx: &Ctx) -> Result<ProcTy, String> {
        match self {
            Proc::PSkip => Ok(ProcTy::empty()),
            Proc::PDebug(k) => {
                println!("Current permission: {0:?}", ctx.perm);
                println!("Current variables: {0:?}", ctx.var_tys);
                k.check(ctx)
            },
            Proc::PCall(p) => {
                if ctx.perm.is_empty() {
                    ctx.proc_tys.get(p).cloned().ok_or("PCall: proc not found".to_string())
                } else {
                    Err("PCall: permission not empty".to_string())
                }
            }
            Proc::Par(p1, p2) => {
                if ctx.perm.is_empty() {
                    p1.check(ctx).and_then(|t1| 
                        p2.check(ctx).and_then(|t2| 
                            t1.try_add(&t2)))
                } else {
                    Err("Par".to_string())
                }
            },
            Proc::PRead(loc, v, k) => {
                if ctx.locations.contains_key(loc) && ctx.perm.contains_read(loc) {
                    k.check(&ctx.extend_var(v))
                }
                else { Err("PRead".to_string()) }
            },
            Proc::PWrite(loc, e, k) => {
                if e.check(ctx) && ctx.locations.contains_key(loc) && ctx.perm.contains_write(loc) {
                    k.check(ctx)
                }
                else { Err("PWrite".to_string()) }
            },
            Proc::PRecv(c, x, k) => {
                match ctx.chan_tys.get(c) {
                    None => Err("Channel not found".to_string()),
                    Some(perm) => 
                        k.check(&ctx.extend_var(x).extend_perm(&perm.0)).and_then(|ctx2| Ok(ctx2.with_input(c)))
                }
            },
            Proc::PSend(c, e, k) => {
                match ctx.chan_tys.get(c) {
                    None => Err("Channel not found".to_string()),
                    Some(perm) => if e.check(ctx) { 
                        ctx.retract_perm(&perm.0).and_then(|ctx2|
                            k.check(&ctx2).and_then(|ctx3|
                                Ok(ctx3.with_output(c))
                            )
                        )
                    }
                    else { Err("Expression error".to_string()) }
                }
            }
        }
    }
}
            
impl Decl {
    pub fn check(&self, ctx : &Ctx) -> Result<Ctx, String> {
        match self {
            Decl::DeclLoc(loc) => {
                if !ctx.locations.contains_key(loc) {
                    Ok(Ctx{locations: ctx.locations.clone().update(loc.clone(), ()), ..ctx.clone()})
                }
                else { Err("DeclLoc".to_string()) }
            },
            Decl::DeclChan(c, p) => {
                if !ctx.chan_tys.contains_key(c) && p.valid(ctx) {
                    Ok(Ctx{chan_tys: ctx.chan_tys.clone().update(c.clone(), ChanTy(p.clone())), ..ctx.clone()})
                }
                else { Err("DeclChan".to_string()) }
            },
            Decl::DeclProc(pn, pty, k) => {
                if !ctx.proc_tys.contains_key(pn) && pty.check(ctx) {
                    let t = k.check(ctx);
                    if t.clone()?.sub_ty(pty) {
                        Ok(Ctx{proc_tys: ctx.proc_tys.clone().update(pn.clone(), pty.clone()), ..ctx.clone()})
                    }
                    else { 
                        let e = format!("Channel subtyping error: got {:?}, expected {:?}", &t, &pty);
                        Err(e)
                    }
                }
                else { Err("Duplicate proc, or invalid proc type".to_string()) }
            }
        }
    }
    
}

pub fn check_decls(ds : Vec<Rc<Decl>>) -> Ctx {
    let mut c = Ctx::new();
    for d in ds {
        match d.check(&c) {
            Err(e) => panic!("Type error: {}", e),
            Ok(c2) => {
                 c = c2.clone()
            }
        }
    }
    c
}
