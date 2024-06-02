use std::rc::Rc;
use std::{borrow::Borrow, fmt};

use indexmap::{IndexMap, IndexSet};

use crate::span::*;

/// Macro for defining string types like
/// pub struct $NAME(Rc<str>);
#[macro_export]
macro_rules! rc_str_type {
    ($typ_name:ident, $fmt_pattern:expr) => {
        #[derive(Hash, Eq, PartialEq, Clone, Debug)]
        pub struct $typ_name(Rc<str>);

        impl From<&$typ_name> for Rc<str> {
            fn from(v: &$typ_name) -> Self {
                v.0.clone()
            }
        }

        impl<S: Into<Rc<str>>> From<S> for $typ_name {
            fn from(v: S) -> Self {
                $typ_name(v.into())
            }
        }

        impl fmt::Display for $typ_name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, $fmt_pattern, self.0)
            }
        }

        impl $typ_name {
            pub fn as_str(&self) -> &str {
                self.0.as_ref()
            }
        }
    };
}

rc_str_type!(MutName, "{}");
rc_str_type!(ChanName, "{}");
rc_str_type!(ProcName, "{}");
rc_str_type!(Var, "{}");
rc_str_type!(Const, "{}");
rc_str_type!(PermVar, "{}");

#[derive(Clone, Copy, Debug)]
pub enum PermFraction {
    /// Write(k) = sum of Read(k), Read(k + 1) ...
    /// Write(0) = all permissions
    Write(u32),
    Read(u32),
}

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum MutReferenceIndex {
    Int(i64),
    BitVec(u64, BitVecWidth),
    Unknown,
}

pub type MutReferenceType = Rc<MutReferenceTypeX>;
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum MutReferenceTypeX {
    Base(MutName),
    Index(MutReferenceType, MutReferenceIndex),
    Offset(MutReferenceType, MutReferenceIndex),
}

pub type MutReference = RcSpanned<MutReferenceX>;
#[derive(Debug)]
pub enum MutReferenceX {
    Base(MutName),
    Deref(Term),
    Index(MutReference, Term),
    Slice(MutReference, Option<Term>, Option<Term>),
}

pub type Permission = RcSpanned<PermissionX>;
#[derive(Debug)]
pub enum PermissionX {
    Empty,
    Add(Permission, Permission),
    Sub(Permission, Permission),
    Ite(Term, Permission, Permission),
    Fraction(PermFraction, MutReference),
    Var(PermVar, Vec<Term>),
}

pub type BitVecWidth = u32;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum BaseType {
    Bool,
    Int,
    BitVec(BitVecWidth),
}

pub type TermType = Rc<TermTypeX>;
#[derive(Eq, PartialEq, Debug)]
pub enum TermTypeX {
    Base(BaseType),
    Ref(Vec<MutReferenceType>),
}

pub type MutType = Rc<MutTypeX>;
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum MutTypeX {
    Base(BaseType),
    Array(BaseType, MutType),
}

pub type Term = RcSpanned<TermX>;
#[derive(Debug)]
pub enum TermX {
    Var(Var),
    Const(Const),
    Bool(bool),
    Int(i64),
    BitVec(u64, BitVecWidth),

    Ref(MutReference),

    // Integer operations
    Add(Term, Term),
    Mul(Term, Term),
    Less(Term, Term),

    // BV operations,
    BVAdd(Term, Term),
    BVMul(Term, Term),
    BVULT(Term, Term),
    BVSLT(Term, Term),
    BVSGT(Term, Term),

    Equal(Term, Term),
    And(Term, Term),
    Not(Term),
}

pub type Proc = RcSpanned<ProcX>;
#[derive(Debug)]
pub enum ProcX {
    Skip,
    Send(ChanName, Term, Proc),
    Recv(ChanName, Var, Proc),
    Write(MutReference, Term, Proc),
    Read(MutReference, Var, Proc),
    Ite(Term, Proc, Proc),
    Call(ProcName, Vec<Term>),
    Par(Proc, Proc),
}

pub type ConstDecl = RcSpanned<ConstDeclX>;
#[derive(Debug)]
pub struct ConstDeclX {
    pub name: Const,
    pub typ: BaseType,
}

pub type PermDecl = RcSpanned<PermDeclX>;
#[derive(Debug)]
pub struct PermDeclX {
    pub name: PermVar,
    pub param_typs: Vec<BaseType>,
}

pub type MutDecl = RcSpanned<MutDeclX>;
#[derive(Debug)]
pub struct MutDeclX {
    pub name: MutName,
    pub typ: MutType,
}

pub type ChanDecl = RcSpanned<ChanDeclX>;
#[derive(Debug)]
pub struct ChanDeclX {
    pub name: ChanName,
    pub typ: TermType,
    pub perm: Permission,
}

#[derive(Clone, Debug)]
pub struct ProcParam {
    pub name: Var,
    pub typ: TermType,
}

pub type ProcResource = RcSpanned<ProcResourceX>;
#[derive(Debug)]
pub enum ProcResourceX {
    Perm(Permission),
    Input(ChanName),
    Output(ChanName),
}

pub type ProcDecl = RcSpanned<ProcDeclX>;
#[derive(Debug)]
pub struct ProcDeclX {
    pub name: ProcName,
    pub params: Vec<ProcParam>,
    pub res: Vec<ProcResource>,
    pub all_res: bool,
    pub body: Proc,
}

#[derive(Debug)]
pub enum Decl {
    Const(ConstDecl),
    Perm(PermDecl),
    Mut(MutDecl),
    Chan(ChanDecl),
    Proc(ProcDecl),
}

pub type Program = Rc<ProgramX>;
pub struct ProgramX {
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub struct Ctx {
    pub consts: IndexMap<Const, ConstDecl>,
    pub perms: IndexMap<PermVar, PermDecl>,
    pub muts: IndexMap<MutName, MutDecl>,
    pub chans: IndexMap<ChanName, ChanDecl>,
    pub procs: IndexMap<ProcName, ProcDecl>,
}

impl ProcResourceX {
    pub fn input(name: impl Into<ChanName>) -> ProcResource {
        Spanned::new(ProcResourceX::Input(name.into()))
    }

    pub fn output(name: impl Into<ChanName>) -> ProcResource {
        Spanned::new(ProcResourceX::Output(name.into()))
    }

    pub fn perm(perm: impl Borrow<Permission>) -> ProcResource {
        Spanned::new(ProcResourceX::Perm(perm.borrow().clone()))
    }
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx {
            consts: IndexMap::new(),
            perms: IndexMap::new(),
            muts: IndexMap::new(),
            chans: IndexMap::new(),
            procs: IndexMap::new(),
        }
    }

    pub fn max_mut_dim(&self) -> usize {
        self.muts
            .values()
            .map(|decl| decl.typ.get_dimensions())
            .max()
            .unwrap_or(0)
    }

    pub fn add_const(&mut self, decl: &ConstDecl) -> Result<(), String> {
        if self.consts.contains_key(&decl.name) {
            Err(format!("duplicate constant declaration {}", decl.name))?;
        }
        self.consts.insert(decl.name.clone(), decl.clone());
        Ok(())
    }

    pub fn add_mut(&mut self, decl: &MutDecl) -> Result<(), String> {
        if self.muts.contains_key(&decl.name) {
            Err(format!("duplicate mutable declaration {}", decl.name))?;
        }
        self.muts.insert(decl.name.clone(), decl.clone());
        Ok(())
    }

    pub fn add_perm(&mut self, decl: &PermDecl) -> Result<(), String> {
        if self.perms.contains_key(&decl.name) {
            Err(format!("duplicate permission variable declaration {}", decl.name))?;
        }
        self.perms.insert(decl.name.clone(), decl.clone());
        Ok(())
    }

    /// Since the parser will conflate variables and constants
    /// here we construct a substitution map from variables to constants
    pub fn const_substitution(&self) -> IndexMap<Var, Term> {
        self.consts.keys().map(|c| (c.into(), TermX::var(c))).collect()
    }

    pub fn add_chan(&mut self, decl: &ChanDecl) -> Result<(), String> {
        if self.chans.contains_key(&decl.name) {
            Err(format!("duplicate channel declaration {}", decl.name))?;
        }

        // Substitute variables => constants
        let perm_subst = PermissionX::substitute(&decl.perm, &self.const_substitution());
        self.chans.insert(
            decl.name.clone(),
            Spanned::spanned_option(
                &decl.span,
                ChanDeclX {
                    name: decl.name.clone(),
                    typ: decl.typ.clone(),
                    perm: perm_subst,
                },
            ),
        );
        Ok(())
    }

    /// Get all possible resources in the current context
    pub fn get_all_res(&self, span: &Option<Span>) -> Vec<ProcResource> {
        let mut res = Vec::new();

        for mut_name in self.muts.keys() {
            // Add write permission to mut_name
            res.push(Spanned::spanned_option(
                span,
                ProcResourceX::Perm(Spanned::spanned_option(
                    span,
                    PermissionX::Fraction(
                        PermFraction::Write(0),
                        Spanned::spanned_option(
                            span,
                            MutReferenceX::Base(mut_name.clone()),
                        ),
                    ),
                )),
            ));
        }

        for chan_name in self.chans.keys() {
            res.push(Spanned::spanned_option(
                span,
                ProcResourceX::Input(chan_name.clone()),
            ));
            res.push(Spanned::spanned_option(
                span,
                ProcResourceX::Output(chan_name.clone()),
            ));
        }

        res
    }

    pub fn add_proc(&mut self, decl: &ProcDecl) -> Result<(), String> {
        if self.procs.contains_key(&decl.name) {
            Err(format!("duplicate process definition {:?}", decl.name))?;
        }

        let mut subst = self.const_substitution();

        // Copy new resources with constants substituted
        let new_res = if decl.all_res {
            // Expand `proc ... | all` ==> `proc ... | write ..., in ...`
            self.get_all_res(&decl.span)
        } else {
            // Substitute variables => constants
            decl.res.iter().map(|r|
                match &r.x {
                    ProcResourceX::Perm(p) => Spanned::spanned_option(
                        &r.span,
                        ProcResourceX::Perm(PermissionX::substitute(p, &subst)),
                    ),
                    _ => r.clone(),
                }).collect()
        };

        // Shadow process's paramters in the variables => constants substitution
        for param in &decl.params {
            subst.shift_remove(&param.name);
        }

        // Substitute the process body
        let new_body = ProcX::substitute(&decl.body, &mut subst);

        self.procs.insert(
            decl.name.clone(),
            Spanned::spanned_option(
                &decl.span,
                ProcDeclX {
                    name: decl.name.clone(),
                    params: decl.params.clone(),
                    res: new_res,
                    all_res: false,
                    body: new_body,
                },
            ),
        );

        Ok(())
    }

    /// Process a parsed AST into a context
    /// This do some preprocessing including
    /// replacing constants and some notations like
    /// "all" resources
    pub fn from(prog: &Program) -> Result<Ctx, String> {
        let mut ctx = Ctx::new();

        // Collect all constants, mutables, and permission variables first
        for decl in &prog.decls {
            match decl {
                Decl::Const(decl) => ctx.add_const(decl)?,
                Decl::Mut(decl) => ctx.add_mut(decl)?,
                Decl::Perm(decl) => ctx.add_perm(decl)?,
                _ => {}
            }
        }

        // Collect channel declarations converting some Var to Const
        for decl in &prog.decls {
            match decl {
                Decl::Chan(decl) => ctx.add_chan(decl)?,
                _ => {}
            }
        }

        // Collect process declarations while converting some Var to Const
        // and also expanding "all" resource notation
        // This needs to happen after add_chan's since the `all` resource
        // notation requires knowing all channels in the context
        for decl in &prog.decls {
            match decl {
                Decl::Proc(decl) => ctx.add_proc(decl)?,
                _ => {}
            }
        }
        Ok(ctx)
    }
}

impl BaseType {
    pub fn is_int(&self) -> bool {
        match self {
            BaseType::Int => true,
            _ => false,
        }
    }

    pub fn is_bv(&self) -> bool {
        match self {
            BaseType::BitVec(..) => true,
            _ => false,
        }
    }
}

impl MutReferenceTypeX {
    pub fn base(name: impl Into<MutName>) -> MutReferenceType {
        Rc::new(MutReferenceTypeX::Base(name.into()))
    }

    pub fn index(base: impl Borrow<MutReferenceType>, index: MutReferenceIndex) -> MutReferenceType {
        Rc::new(MutReferenceTypeX::Index(base.borrow().clone(), index))
    }

    pub fn offset(base: impl Borrow<MutReferenceType>, offset: MutReferenceIndex) -> MutReferenceType {
        Rc::new(MutReferenceTypeX::Offset(base.borrow().clone(), offset))
    }
}

impl TermTypeX {
    pub fn is_int(&self) -> bool {
        match self {
            TermTypeX::Base(BaseType::Int) => true,
            _ => false,
        }
    }

    pub fn is_bv(&self) -> bool {
        match self {
            TermTypeX::Base(BaseType::BitVec(..)) => true,
            _ => false,
        }
    }

    pub fn is_int_or_bv(&self) -> bool {
        match self {
            TermTypeX::Base(BaseType::Int) => true,
            TermTypeX::Base(BaseType::BitVec(..)) => true,
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            TermTypeX::Base(BaseType::Bool) => true,
            _ => false,
        }
    }

    pub fn is_ref(&self) -> bool {
        match self {
            TermTypeX::Ref(..) => true,
            _ => false,
        }
    }

    pub fn is_base(&self, typ: &BaseType) -> bool {
        match self {
            TermTypeX::Base(base) => base == typ,
            _ => false,
        }
    }

    pub fn base(typ: &BaseType) -> TermType {
        Rc::new(TermTypeX::Base(typ.clone()))
    }

    pub fn int() -> TermType {
        Rc::new(TermTypeX::Base(BaseType::Int))
    }

    pub fn bit_vec(w: BitVecWidth) -> TermType {
        Rc::new(TermTypeX::Base(BaseType::BitVec(w)))
    }

    pub fn bool() -> TermType {
        Rc::new(TermTypeX::Base(BaseType::Bool))
    }

    pub fn mut_ref(ref_types: impl IntoIterator<Item=impl Borrow<MutReferenceType>>) -> TermType {
        Rc::new(TermTypeX::Ref(ref_types.into_iter().map(|r| r.borrow().clone()).collect()))
    }
}

macro_rules! substitute_inplace {
    // Unary constructs
    ($term:expr, $op:expr, $k:ident, $t:expr, $subst:expr) => {
        {
            let t_subst = $k::substitute_inplace($t, $subst);
            if t_subst.is_some() {
                Some(Spanned::spanned_option(
                    &$term.borrow().span,
                    $op(t_subst.unwrap()),
                ))
            } else {
                None
            }
        }
    };

    // Binary constructs
    ($term:expr, $op:expr, $k1:ident, $t1:expr, $k2:ident, $t2:expr, $subst:expr) => {
        {
            let t1_subst = $k1::substitute_inplace($t1, $subst);
            let t2_subst = $k2::substitute_inplace($t2, $subst);
            if t1_subst.is_some() || t2_subst.is_some() {
                Some(Spanned::spanned_option(
                    &$term.borrow().span,
                    $op(
                        t1_subst.unwrap_or($t1.clone()),
                        t2_subst.unwrap_or($t2.clone()),
                    ),
                ))
            } else {
                None
            }
        }
    };

    // Ternary constructs
    ($term:expr, $op:expr, $k1:ident, $t1:expr, $k2:ident, $t2:expr, $k3:ident, $t3:expr, $subst:expr) => {
        {
            let t1_subst = $k1::substitute_inplace($t1, $subst);
            let t2_subst = $k2::substitute_inplace($t2, $subst);
            let t3_subst = $k3::substitute_inplace($t3, $subst);
            if t1_subst.is_some() || t2_subst.is_some() || t3_subst.is_some() {
                Some(Spanned::spanned_option(
                    &$term.borrow().span,
                    $op(
                        t1_subst.unwrap_or($t1.clone()),
                        t2_subst.unwrap_or($t2.clone()),
                        t3_subst.unwrap_or($t3.clone()),
                    ),
                ))
            } else {
                None
            }
        }
    };
}

impl TermX {
    pub fn var(v: impl Into<Var>) -> Term {
        Spanned::new(TermX::Var(v.into()))
    }

    pub fn int(i: i64) -> Term {
        Spanned::new(TermX::Int(i))
    }

    pub fn bit_vec(i: u64, w: BitVecWidth) -> Term {
        Spanned::new(TermX::BitVec(i, w))
    }

    pub fn constant(c: impl Into<Const>) -> Term {
        Spanned::new(TermX::Const(c.into()))
    }

    pub fn reference(m: impl Borrow<MutReference>) -> Term {
        Spanned::new(TermX::Ref(m.borrow().clone()))
    }

    pub fn bvadd(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::BVAdd(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn bvmul(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::BVMul(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn bvult(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::BVULT(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn bvslt(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::BVSLT(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn bvsgt(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::BVSGT(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn eq(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::Equal(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn less(t1: impl Borrow<Term>, t2: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::Less(t1.borrow().clone(), t2.borrow().clone()))
    }

    pub fn not(t: impl Borrow<Term>) -> Term {
        Spanned::new(TermX::Not(t.borrow().clone()))
    }

    /// Returns Some if the term is substituted, None if unchanged
    fn substitute_inplace(term: impl Borrow<Term>, subst: &IndexMap<Var, Term>) -> Option<Term> {
        match &term.borrow().x {
            TermX::Var(var) => Some(subst.get(var)?.clone()),
            TermX::Const(..) => None,
            TermX::Bool(..) => None,
            TermX::Int(..) => None,
            TermX::BitVec(..) => None,
            TermX::Ref(m) => substitute_inplace!(term, TermX::Ref, MutReferenceX, m, subst),
            TermX::Add(t1, t2) => substitute_inplace!(term, TermX::Add, TermX, t1, TermX, t2, subst),
            TermX::BVAdd(t1, t2) => substitute_inplace!(term, TermX::BVAdd, TermX, t1, TermX, t2, subst),
            TermX::Mul(t1, t2) => substitute_inplace!(term, TermX::Mul, TermX, t1, TermX, t2, subst),
            TermX::BVMul(t1, t2) => substitute_inplace!(term, TermX::BVMul, TermX, t1, TermX, t2, subst),
            TermX::And(t1, t2) => substitute_inplace!(term, TermX::And, TermX, t1, TermX, t2, subst),
            TermX::Less(t1, t2) => substitute_inplace!(term, TermX::Less, TermX, t1, TermX, t2, subst),
            TermX::BVULT(t1, t2) => substitute_inplace!(term, TermX::BVULT, TermX, t1, TermX, t2, subst),
            TermX::BVSLT(t1, t2) => substitute_inplace!(term, TermX::BVSLT, TermX, t1, TermX, t2, subst),
            TermX::BVSGT(t1, t2) => substitute_inplace!(term, TermX::BVSGT, TermX, t1, TermX, t2, subst),
            TermX::Equal(t1, t2) => substitute_inplace!(term, TermX::Equal, TermX, t1, TermX, t2, subst),
            TermX::Not(t) => substitute_inplace!(term, TermX::Not, TermX, t, subst),
        }
    }

    /// Substitutes into a term without modifying unchanged subtrees
    pub fn substitute(term: impl Borrow<Term>, subst: &IndexMap<Var, Term>) -> Term {
        Self::substitute_inplace(term.borrow(), subst).unwrap_or(term.borrow().clone())
    }

    fn free_vars_inplace(&self, vars: &mut IndexSet<Var>) {
        match self {
            TermX::Var(var) => {
                vars.insert(var.clone());
            }
            TermX::Const(..) => {}
            TermX::Bool(..) => {}
            TermX::Int(..) => {}
            TermX::BitVec(..) => {}
            TermX::Ref(m) => {
                m.free_vars_inplace(vars);
            }
            TermX::Add(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::BVAdd(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Mul(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::BVMul(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::And(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Less(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::BVULT(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::BVSLT(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::BVSGT(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Equal(t1, t2) => {
                t1.free_vars_inplace(vars);
                t2.free_vars_inplace(vars);
            }
            TermX::Not(t) => {
                t.free_vars_inplace(vars);
            }
        }
    }

    pub fn free_vars(&self) -> IndexSet<Var> {
        let mut vars = IndexSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }

    /// Precedence of the top level operator
    fn precedence(&self) -> u32 {
        match self {
            TermX::Var(..) => 0,
            TermX::Const(..) => 0,
            TermX::Bool(..) => 0,
            TermX::Int(..) => 0,
            TermX::BitVec(..) => 0,
            TermX::Ref(..) => 0,
            TermX::Add(..) => 2,
            TermX::BVAdd(..) => 2,
            TermX::Mul(..) => 1,
            TermX::BVMul(..) => 1,
            TermX::And(..) => 5,
            TermX::Less(..) => 3,
            TermX::BVULT(..) => 3,
            TermX::BVSLT(..) => 3,
            TermX::BVSGT(..) => 3,
            TermX::Equal(..) => 3,
            TermX::Not(..) => 4,
        }
    }
}

impl MutTypeX {
    pub fn base(base: impl Borrow<BaseType>) -> MutType {
        Rc::new(MutTypeX::Base(base.borrow().clone()))
    }
    
    pub fn array(index: impl Borrow<BaseType>, base: impl Borrow<MutType>) -> MutType {
        Rc::new(MutTypeX::Array(index.borrow().clone(), base.borrow().clone()))
    }

    pub fn get_dimensions(&self) -> usize {
        match self {
            MutTypeX::Base(..) => 0,
            MutTypeX::Array(_, t) => t.get_dimensions() + 1,
        }
    }
}

impl MutReferenceX {
    pub fn base(name: impl Into<MutName>) -> MutReference {
        Spanned::new(MutReferenceX::Base(name.into()))
    }

    pub fn deref(term: impl Borrow<Term>) -> MutReference {
        Spanned::new(MutReferenceX::Deref(term.borrow().clone()))
    }

    pub fn index(m: impl Borrow<MutReference>, i: impl Borrow<Term>) -> MutReference {
        Spanned::new(MutReferenceX::Index(m.borrow().clone(), i.borrow().clone()))
    }

    pub fn slice(m: impl Borrow<MutReference>, i: Option<&Term>, j: Option<&Term>) -> MutReference {
        Spanned::new(MutReferenceX::Slice(m.borrow().clone(), i.map(|i| i.clone()), j.map(|j| j.clone())))
    }

    /// Check if the mutable reference has a deref or not
    pub fn has_deref(&self) -> bool {
        match self {
            MutReferenceX::Base(..) => false,
            MutReferenceX::Deref(..) => true,
            MutReferenceX::Index(m, ..) => m.has_deref(),
            MutReferenceX::Slice(m, ..) => m.has_deref(),
        }
    }

    /// Get the base mutable name if it exists
    pub fn get_base_mutable(&self) -> Option<MutName> {
        match self {
            MutReferenceX::Base(n) => Some(n.clone()),
            MutReferenceX::Deref(..) => None,
            MutReferenceX::Index(m, ..) => m.get_base_mutable(),
            MutReferenceX::Slice(m, ..) => m.get_base_mutable(),
        }
    }

    fn free_vars_inplace(&self, vars: &mut IndexSet<Var>) {
        match self {
            MutReferenceX::Base(..) => {}
            MutReferenceX::Deref(t) => {
                t.free_vars_inplace(vars);
            }
            MutReferenceX::Index(m, t) => {
                m.free_vars_inplace(vars);
                TermX::free_vars_inplace(t, vars);
            }
            MutReferenceX::Slice(m, t1, t2) => {
                m.free_vars_inplace(vars);
                if let Some(t1) = t1 {
                    TermX::free_vars_inplace(t1, vars);
                }
                if let Some(t2) = t2 {
                    TermX::free_vars_inplace(t2, vars);
                }
            }
        }
    }

    /// Returns None if unchanged
    fn substitute_inplace(
        mut_ref: impl Borrow<MutReference>,
        subst: &IndexMap<Var, Term>,
    ) -> Option<MutReference> {
        match &mut_ref.borrow().x {
            MutReferenceX::Base(..) => None,
            MutReferenceX::Deref(t) => substitute_inplace!(mut_ref, MutReferenceX::Deref, TermX, t, subst),
            MutReferenceX::Index(m, t) => substitute_inplace!(mut_ref, MutReferenceX::Index, MutReferenceX, m, TermX, t, subst),
            MutReferenceX::Slice(m, t1, t2) => {
                let m_subst = Self::substitute_inplace(m, subst);
                let t1_subst = t1
                    .as_ref()
                    .map(|t| TermX::substitute_inplace(t, subst))
                    .flatten();
                let t2_subst = t2
                    .as_ref()
                    .map(|t| TermX::substitute_inplace(t, subst))
                    .flatten();
                if m_subst.is_some() || t1_subst.is_some() || t2_subst.is_some() {
                    Some(Spanned::spanned_option(
                        &mut_ref.borrow().span,
                        MutReferenceX::Slice(
                            m_subst.unwrap_or(m.clone()),
                            if t1.is_some() {
                                Some(t1_subst.unwrap_or(t1.as_ref().unwrap().clone()))
                            } else {
                                None
                            },
                            if t2.is_some() {
                                Some(t2_subst.unwrap_or(t2.as_ref().unwrap().clone()))
                            } else {
                                None
                            },
                        ),
                    ))
                } else {
                    None
                }
            }
        }
    }
}

impl ProcX {
    pub fn skip() -> Proc {
        Spanned::new(ProcX::Skip)
    }

    pub fn send(c: impl Into<ChanName>, t: impl Borrow<Term>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Send(
            c.into(),
            t.borrow().clone(),
            p.borrow().clone(),
        ))
    }

    pub fn recv(c: impl Into<ChanName>, v: impl Into<Var>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Recv(c.into(), v.into(), p.borrow().clone()))
    }

    pub fn write(m: impl Borrow<MutReference>, t: impl Borrow<Term>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Write(
            m.borrow().clone(),
            t.borrow().clone(),
            p.borrow().clone(),
        ))
    }

    pub fn read(m: impl Borrow<MutReference>, v: impl Into<Var>, p: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Read(
            m.borrow().clone(),
            v.into(),
            p.borrow().clone(),
        ))
    }

    pub fn ite(t: impl Borrow<Term>, p1: impl Borrow<Proc>, p2: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Ite(
            t.borrow().clone(),
            p1.borrow().clone(),
            p2.borrow().clone(),
        ))
    }

    pub fn par(p1: impl Borrow<Proc>, p2: impl Borrow<Proc>) -> Proc {
        Spanned::new(ProcX::Par(p1.borrow().clone(), p2.borrow().clone()))
    }

    pub fn call(
        name: impl Into<ProcName>,
        args: impl IntoIterator<Item = impl Borrow<Term>>,
    ) -> Proc {
        Spanned::new(ProcX::Call(
            name.into(),
            args.into_iter().map(|t| t.borrow().clone()).collect(),
        ))
    }
    
    /// Returns None if unchanged
    // TODO: this functinon currently assumes no capturing of variables
    fn substitute_inplace(
        proc: impl Borrow<Proc>,
        subst: &mut IndexMap<Var, Term>,
    ) -> Option<Proc> {
        match &proc.borrow().x {
            ProcX::Skip => None,
            ProcX::Send(c, t, p) => {
                let t_subst = TermX::substitute_inplace(t, subst);
                let p_subst = Self::substitute_inplace(p, subst);

                if t_subst.is_some() || p_subst.is_some() {
                    Some(ProcX::send(
                        c,
                        &t_subst.unwrap_or(t.clone()),
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Recv(c, v, p) => {
                let p_subst = if let Some(t) = subst.get(v) {
                    let t_clone = t.clone();
                    subst.shift_remove(v);
                    let p_subst = Self::substitute_inplace(p, subst);
                    subst.insert(v.clone(), t_clone); // TODO: might mess up the order of terms
                    p_subst
                } else {
                    Self::substitute_inplace(p, subst)
                };

                if p_subst.is_some() {
                    Some(ProcX::recv(c, v, &p_subst.unwrap_or(p.clone())))
                } else {
                    None
                }
            }
            ProcX::Write(m, t, p) => {
                let m_subst = MutReferenceX::substitute_inplace(m, subst);
                let t_subst = TermX::substitute_inplace(t, subst);
                let p_subst = Self::substitute_inplace(p, subst);

                if m_subst.is_some() || t_subst.is_some() || p_subst.is_some() {
                    Some(ProcX::write(
                        &m_subst.unwrap_or(m.clone()),
                        &t_subst.unwrap_or(t.clone()),
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Read(m, v, p) => {
                let m_subst = MutReferenceX::substitute_inplace(m, subst);
                let p_subst = if let Some(t) = subst.get(v) {
                    let t_clone = t.clone();
                    subst.shift_remove(v);
                    let p_subst = Self::substitute_inplace(p, subst);
                    subst.insert(v.clone(), t_clone); // TODO: might mess up the order of terms
                    p_subst
                } else {
                    Self::substitute_inplace(p, subst)
                };

                if m_subst.is_some() || p_subst.is_some() {
                    Some(ProcX::read(
                        &m_subst.unwrap_or(m.clone()),
                        v,
                        &p_subst.unwrap_or(p.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Ite(t, p1, p2) => {
                let t_subst = TermX::substitute_inplace(t, subst);
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if t_subst.is_some() || p1_subst.is_some() || p2_subst.is_some() {
                    Some(ProcX::ite(
                        &t_subst.unwrap_or(t.clone()),
                        &p1_subst.unwrap_or(p1.clone()),
                        &p2_subst.unwrap_or(p2.clone()),
                    ))
                } else {
                    None
                }
            }
            ProcX::Call(n, args) => {
                let mut new_args = Vec::new();
                let mut changed = false;

                for arg in args {
                    let arg_subst = TermX::substitute_inplace(arg, subst);
                    if let Some(arg_subst) = arg_subst {
                        changed = true;
                        new_args.push(arg_subst);
                    } else {
                        new_args.push(arg.clone());
                    }
                }

                if changed {
                    Some(ProcX::call(n, &new_args))
                } else {
                    None
                }
            }
            ProcX::Par(p1, p2) => {
                let p1_subst = Self::substitute_inplace(p1, subst);
                let p2_subst = Self::substitute_inplace(p2, subst);

                if p1_subst.is_some() || p2_subst.is_some() {
                    Some(ProcX::par(
                        &p1_subst.unwrap_or(p1.clone()),
                        &p2_subst.unwrap_or(p2.clone()),
                    ))
                } else {
                    None
                }
            }
        }
    }

    /// Substitutes into a permission without modifying unchanged subtrees
    pub fn substitute(p: impl Borrow<Proc>, subst: &mut IndexMap<Var, Term>) -> Proc {
        Self::substitute_inplace(p.borrow(), subst).unwrap_or(p.borrow().clone())
    }
}

impl PermissionX {
    pub fn is_empty(&self) -> bool {
        match self {
            PermissionX::Empty => true,
            _ => false,
        }
    }

    pub fn empty() -> Permission {
        Spanned::new(PermissionX::Empty)
    }

    pub fn var(var: impl Into<PermVar>, terms: impl IntoIterator<Item=impl Borrow<Term>>) -> Permission {
        Spanned::new(PermissionX::Var(var.into(), terms.into_iter().map(|t| t.borrow().clone()).collect()))
    }

    pub fn add(p1: impl Borrow<Permission>, p2: impl Borrow<Permission>) -> Permission {
        if p1.borrow().is_empty() {
            p2.borrow().clone()
        } else if p2.borrow().is_empty() {
            p1.borrow().clone()
        } else {
            Spanned::new(PermissionX::Add(p1.borrow().clone(), p2.borrow().clone()))
        }
    }

    pub fn sub(p1: impl Borrow<Permission>, p2: impl Borrow<Permission>) -> Permission {
        if p2.borrow().is_empty() {
            p1.borrow().clone()
        } else {
            Spanned::new(PermissionX::Sub(p1.borrow().clone(), p2.borrow().clone()))
        }
    }

    /// Returns Some if the term is substituted, None if unchanged
    fn substitute_inplace(
        perm: impl Borrow<Permission>,
        subst: &IndexMap<Var, Term>,
    ) -> Option<Permission> {
        match &perm.borrow().x {
            PermissionX::Empty => None,
            PermissionX::Add(p1, p2) => substitute_inplace!(perm, PermissionX::Add, PermissionX, p1, PermissionX, p2, subst),
            PermissionX::Sub(p1, p2) => substitute_inplace!(perm, PermissionX::Sub, PermissionX, p1, PermissionX, p2, subst),
            PermissionX::Ite(t, p1, p2) => substitute_inplace!(perm, PermissionX::Ite, TermX, t, PermissionX, p1, PermissionX, p2, subst),
            PermissionX::Fraction(frac, mut_ref) => {
                let mut_ref_subst = MutReferenceX::substitute_inplace(mut_ref, subst);
                if mut_ref_subst.is_some() {
                    Some(Spanned::spanned_option(
                        &perm.borrow().span,
                        PermissionX::Fraction(*frac, mut_ref_subst.unwrap()),
                    ))
                } else {
                    None
                }
            }
            PermissionX::Var(v, terms) => {
                let mut terms_subst = Vec::new();
                let mut modified = false;

                for term in terms {
                    let term_subst = TermX::substitute_inplace(term, subst);
                    if let Some(term_subst) = term_subst {
                        modified = true;
                        terms_subst.push(term_subst);
                    } else {
                        terms_subst.push(term.clone());
                    }
                }

                if modified {
                    Some(Spanned::spanned_option(
                        &perm.borrow().span,
                        PermissionX::Var(v.clone(), terms_subst),
                    ))
                } else {
                    None
                }
            }
        }
    }

    /// Substitutes into a permission without modifying unchanged subtrees
    pub fn substitute(perm: impl Borrow<Permission>, subst: &IndexMap<Var, Term>) -> Permission {
        Self::substitute_inplace(perm.borrow(), subst).unwrap_or(perm.borrow().clone())
    }

    pub fn substitute_one(
        perm: impl Borrow<Permission>,
        var: impl Into<Var>,
        subterm: impl Borrow<Term>,
    ) -> Permission {
        PermissionX::substitute(
            perm,
            &IndexMap::from([(var.into(), subterm.borrow().clone())]),
        )
    }

    fn free_vars_inplace(&self, vars: &mut IndexSet<Var>) {
        match self {
            PermissionX::Empty => {}
            PermissionX::Add(p1, p2) => {
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Sub(p1, p2) => {
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Ite(t, p1, p2) => {
                t.free_vars_inplace(vars);
                p1.free_vars_inplace(vars);
                p2.free_vars_inplace(vars);
            }
            PermissionX::Fraction(_, mut_ref) => {
                mut_ref.free_vars_inplace(vars);
            }
            PermissionX::Var(_, terms) => {
                for t in terms {
                    t.free_vars_inplace(vars);
                }
            }
        }
    }

    pub fn free_vars(&self) -> IndexSet<Var> {
        let mut vars = IndexSet::new();
        self.free_vars_inplace(&mut vars);
        return vars;
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BaseType::Bool => write!(f, "bool"),
            BaseType::Int => write!(f, "int"),
            BaseType::BitVec(width) => write!(f, "bv{}", width)
        }
    }
}

impl fmt::Display for TermTypeX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermTypeX::Base(t) => write!(f, "{}", t),
            TermTypeX::Ref(refs) => {
                if refs.len() == 1 {
                    write!(f, "&")?;
                } else {
                    write!(f, "&{{")?;
                }

                for (i, mut_ref) in refs.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", mut_ref)?;
                    } else {
                        write!(f, ", {}", mut_ref)?;
                    }
                }

                if refs.len() == 1 {
                    Ok(())
                } else {
                    write!(f, "}}")
                }
            }
        }
    }
}

impl fmt::Display for MutTypeX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutTypeX::Base(base) => write!(f, "{}", base),
            MutTypeX::Array(index, base) => write!(f, "array({}, {})", index, base),
        }
    }
}

impl fmt::Display for TermX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermX::Var(var) => write!(f, "{}", var),
            TermX::Const(c) => write!(f, "{}", c),
            TermX::Bool(b) => write!(f, "{}", b),
            TermX::Int(i) => write!(f, "{}", i),
            TermX::BitVec(i, w) => write!(f, "{}bv{}", i, w),
            TermX::Ref(m) => write!(f, "&{}", m),
            TermX::Add(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " + {}", t2)?;
                } else {
                    write!(f, " + ({})", t2)?;
                }
                Ok(())
            }
            TermX::BVAdd(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " +bv {}", t2)?;
                } else {
                    write!(f, " +bv ({})", t2)?;
                }
                Ok(())
            }
            TermX::Mul(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " * {}", t2)?;
                } else {
                    write!(f, " * ({})", t2)?;
                }
                Ok(())
            }
            TermX::BVMul(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " *bv {}", t2)?;
                } else {
                    write!(f, " *bv ({})", t2)?;
                }
                Ok(())
            }
            TermX::And(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " and {}", t2)?;
                } else {
                    write!(f, " and ({})", t2)?;
                }
                Ok(())
            }
            TermX::Less(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " < {}", t2)?;
                } else {
                    write!(f, " < ({})", t2)?;
                }
                Ok(())
            }
            TermX::BVULT(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " u< {}", t2)?;
                } else {
                    write!(f, " u< ({})", t2)?;
                }
                Ok(())
            }
            TermX::BVSLT(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " s< {}", t2)?;
                } else {
                    write!(f, " s< ({})", t2)?;
                }
                Ok(())
            }
            TermX::BVSGT(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " s> {}", t2)?;
                } else {
                    write!(f, " s> ({})", t2)?;
                }
                Ok(())
            }
            TermX::Equal(t1, t2) => {
                if t1.precedence() <= self.precedence() {
                    write!(f, "{}", t1)?;
                } else {
                    write!(f, "({})", t1)?;
                }
                if t2.precedence() <= self.precedence() {
                    write!(f, " = {}", t2)?;
                } else {
                    write!(f, " = ({})", t2)?;
                }
                Ok(())
            }
            TermX::Not(t) => {
                if t.precedence() <= self.precedence() {
                    write!(f, "not {}", t)?;
                } else {
                    write!(f, "not ({})", t)?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for PermFraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermFraction::Write(k) => write!(f, "write({})", k),
            PermFraction::Read(k) => write!(f, "read({})", k),
        }
    }
}

impl fmt::Display for MutReferenceIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutReferenceIndex::Int(i) => write!(f, "{}", i),
            MutReferenceIndex::BitVec(i, w) => write!(f, "{}bv{}", i, w),
            MutReferenceIndex::Unknown => write!(f, "*"),
        }
    }
}

impl fmt::Display for MutReferenceTypeX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutReferenceTypeX::Base(name) => write!(f, "{}", name),
            MutReferenceTypeX::Index(m, i) => write!(f, "{}[{}]", m, i),
            MutReferenceTypeX::Offset(m, i) => write!(f, "{}[{}..]", m, i),
        }
    }
}

impl fmt::Display for MutReferenceX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutReferenceX::Base(name) => write!(f, "{}", name),
            MutReferenceX::Deref(t) => {
                if TermX::precedence(t) > 0 {
                    write!(f, "*{}", t)
                } else {
                    write!(f, "*({})", t)
                }
            }
            MutReferenceX::Index(m, t) => write!(f, "{}[{}]", m, t),
            MutReferenceX::Slice(m, t1, t2) => {
                write!(f, "{}[", m)?;
                if let Some(t1) = t1 {
                    write!(f, "{}", t1)?;
                }
                write!(f, "..")?;
                if let Some(t2) = t2 {
                    write!(f, "{}", t2)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl fmt::Display for PermissionX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermissionX::Empty => write!(f, "0"),
            PermissionX::Add(p1, p2) => {
                if match &p2.x {
                    PermissionX::Sub(..) => true,
                    _ => false,
                } {
                    write!(f, "{} + ({})", p1, p2)
                } else {
                    write!(f, "{} + {}", p1, p2)
                }
            }
            PermissionX::Sub(p1, p2) => {
                if match &p2.x {
                    PermissionX::Add(..) => true,
                    PermissionX::Sub(..) => true,
                    _ => false,
                } {
                    write!(f, "{} - ({})", p1, p2)
                } else {
                    write!(f, "{} - {}", p1, p2)
                }
            }
            PermissionX::Ite(t, p1, p2) => write!(f, "if {} then {} else {} end", t, p1, p2),
            PermissionX::Fraction(frac, mut_ref) => write!(f, "{} {}", frac, mut_ref),
            PermissionX::Var(v, ts) => {
                write!(f, "{}(", v)?;
                for (i, t) in ts.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", t)?;
                    } else {
                        write!(f, ", {}", t)?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for ConstDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "const {}: {}", self.name, self.typ)
    }
}

impl fmt::Display for PermDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "perm {}(", self.name)?;
        for (i, typ) in self.param_typs.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", typ)?;
            } else {
                write!(f, ", {}", typ)?;
            }
        }
        write!(f, ")")
    }
}

impl fmt::Display for MutDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "mut {}: {}", self.name, self.typ)
    }
}

impl fmt::Display for ChanDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "chan {}: {} | {}", self.name, self.typ, self.perm)
    }
}

impl fmt::Display for ProcParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

impl fmt::Display for ProcResourceX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProcResourceX::Perm(p) => write!(f, "{}", p),
            ProcResourceX::Input(n) => write!(f, "in {}", n),
            ProcResourceX::Output(n) => write!(f, "out {}", n),
        }
    }
}

impl fmt::Display for ProcX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProcX::Skip => write!(f, "skip"),
            ProcX::Send(c, t, p) => write!(f, "send {} -> {}; {}", t, c, p),
            ProcX::Recv(c, v, p) => write!(f, "recv {} <- {}; {}", v, c, p),
            ProcX::Write(m, t, p) => write!(f, "write {} -> {}; {}", t, m, p),
            ProcX::Read(m, v, p) => write!(f, "read {} <- {}; {}", v, m, p),
            ProcX::Ite(t, p1, p2) => write!(f, "if {} then {} else {} end", t, p1, p2),
            ProcX::Call(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i == 0 {
                        write!(f, "{}", arg)?;
                    } else {
                        write!(f, ", {}", arg)?;
                    }
                }
                write!(f, ")")
            }
            ProcX::Par(p1, p2) => write!(f, "({} || {})", p1, p2),
        }
    }
}

impl fmt::Display for ProcDeclX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "proc {}(", self.name)?;
        for (i, param) in self.params.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", param)?;
            } else {
                write!(f, ", {}", param)?;
            }
        }
        write!(f, ")")?;

        if self.all_res {
            write!(f, " | all")?;
        } else {
            for (i, res) in self.res.iter().enumerate() {
                if i == 0 {
                    write!(f, " | {}", res)?;
                } else {
                    write!(f, ", {}", res)?;
                }
            }
        }

        write!(f, " = {}", self.body)
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Decl::Const(decl) => write!(f, "{}", decl),
            Decl::Perm(decl) => write!(f, "{}", decl),
            Decl::Mut(decl) => write!(f, "{}", decl),
            Decl::Chan(decl) => write!(f, "{}", decl),
            Decl::Proc(decl) => write!(f, "{}", decl),
        }
    }
}

impl fmt::Display for ProgramX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for decl in &self.decls {
            writeln!(f, "{}", decl)?;
        }
        Ok(())
    }
}
