/**
 * Semantically, for example,
 * if mut A: [[int]]
 * [write A] := write A[i][j] for all i, j
 * [write A[n..m]] := write A[i][j] for any n <= i < m, and any j
 */

/// AST for permission constraints

use std::fmt;
use std::rc::Rc;

use indexmap::IndexMap;

use crate::{ast::*, check::LocalCtx, smt::{self, EncodingCtx}, span::Spanned};

pub type PermConstraint = Rc<PermConstraintX>;
#[derive(Debug)]
pub enum PermConstraintX {
    LessEq(Permission, Permission),
    Disjoint(Vec<Permission>),
    HasRead(MutReference, Permission),
    HasWrite(MutReference, Permission),
}

#[derive(Debug)]
pub struct PermJudgment {
    pub local: LocalCtx,
    pub local_constraints: Vec<Term>,
    pub perm_constraint: PermConstraint,
}

impl fmt::Display for PermJudgment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.local)?;
        for local_constraint in &self.local_constraints {
            write!(f, ", {}", local_constraint)?;
        }
        write!(f, " |= {}", self.perm_constraint)
    }
}

impl BaseType {
    pub fn as_smt_sort(&self) -> Option<smt::Sort> {
        match self {
            BaseType::Bool => Some(smt::Sort::Bool),
            BaseType::Int => Some(smt::Sort::Int),
            BaseType::Ref(..) => None, // unsupported yet
        }
    }
}

impl Ctx {
    /// Get the unique index of a mutable
    /// based on the order it is defined
    /// This is used for the SMT encoding of permissions
    fn get_mut_index(&self, name: &MutName) -> Option<usize> {
        return self.muts.get_index_of(name)
    }
}

impl TermX {
    /// Encode the term as an SMT term
    /// All free variables and constants are introduced as SMT constants
    pub fn as_smt_term(
        &self,
        const_interp: &IndexMap<Const, smt::Term>,
        var_interp: &IndexMap<Var, smt::Term>,
    ) -> Result<smt::Term, String> {
        match self {
            TermX::Var(v) => var_interp.get(v).cloned().ok_or(format!("undefined variable {v}")),
            TermX::Const(c) => const_interp.get(c).cloned().ok_or(format!("undefined constant {c}")),
            TermX::Bool(b) => Ok(smt::TermX::bool(*b)),
            TermX::Int(i) => if *i >= 0 {
                Ok(smt::TermX::int(*i as u64))
            } else {
                Ok(smt::TermX::neg(smt::TermX::int(-i as u64)))
            }
            TermX::Ref(..) => unimplemented!("reference"),
            TermX::Add(t1, t2) =>
                Ok(smt::TermX::add(
                    t1.as_smt_term(const_interp, var_interp)?,
                    t2.as_smt_term(const_interp, var_interp)?,
                )),
            TermX::Mul(t1, t2) =>
                Ok(smt::TermX::mul(
                    t1.as_smt_term(const_interp, var_interp)?,
                    t2.as_smt_term(const_interp, var_interp)?,
                )),
            TermX::And(t1, t2) =>
                Ok(smt::TermX::and([
                    t1.as_smt_term(const_interp, var_interp)?,
                    t2.as_smt_term(const_interp, var_interp)?,
                ])),
            TermX::Less(t1, t2) =>
                Ok(smt::TermX::lt(
                    t1.as_smt_term(const_interp, var_interp)?,
                    t2.as_smt_term(const_interp, var_interp)?,
                )),
            TermX::Equal(t1, t2) =>
                Ok(smt::TermX::eq(
                    t1.as_smt_term(const_interp, var_interp)?,
                    t2.as_smt_term(const_interp, var_interp)?,
                )),
            TermX::Not(t) =>
                Ok(smt::TermX::not(t.as_smt_term(const_interp, var_interp)?)),
        }
    }
}

impl PermissionX {
    /// Encode a permission as an SMT term indicating whether
    /// the permission is true at the given mutable, indices, and fraction index
    pub fn as_smt_term(
        &self,
        ctx: &Ctx,

        const_interp: &IndexMap<Const, smt::Term>,
        var_interp: &IndexMap<Var, smt::Term>,
        mut_idx: &smt::Term,
        indices: &[smt::Term],
        frac_idx: &smt::Term,
    ) -> Result<smt::Term, String> {
        match self {
            PermissionX::Empty => Ok(smt::TermX::bool(false)),
            PermissionX::Add(p1, p2) =>
                Ok(smt::TermX::or([
                    p1.as_smt_term(ctx, const_interp, var_interp, mut_idx, indices, frac_idx)?,
                    p2.as_smt_term(ctx, const_interp, var_interp, mut_idx, indices, frac_idx)?,
                ])),
            PermissionX::Sub(p1, p2) =>
                Ok(smt::TermX::and([
                    p1.as_smt_term(ctx, const_interp, var_interp, mut_idx, indices, frac_idx)?,
                    smt::TermX::not(p2.as_smt_term(ctx, const_interp, var_interp, mut_idx, indices, frac_idx)?,),
                ])),
            PermissionX::Ite(t, p1, p2) =>
                Ok(smt::TermX::ite(
                    t.as_smt_term(const_interp, var_interp)?,
                    p1.as_smt_term(ctx, const_interp, var_interp, mut_idx, indices, frac_idx)?,
                    p2.as_smt_term(ctx, const_interp, var_interp, mut_idx, indices, frac_idx)?,
                )),
            PermissionX::Fraction(frac, mut_ref) => {
                // Conditinos for the permission to be true at the given location
                let mut conditions = Vec::new();

                // If the fraction does not match, the permission is always empty
                if let PermFraction::Read(k) = frac {
                    conditions.push(smt::TermX::eq(frac_idx, smt::TermX::int(*k as u64)));
                }

                // Check if the indices are within the bound
                // indices = [ i_1, ..., i_n ]
                // where i_1 are the index for the outermost dimension
                let mut rem_mut_ref = mut_ref;
                let mut index_ranges = Vec::new();

                // In a mutable reference A[s_1][s_2]..[s_m]
                // Extract the slices and put them in a vector
                // index_ranges = [ s_m, ..., s_2, s_1 ]
                loop {
                    match &rem_mut_ref.x {
                        MutReferenceX::Base(base) => {
                            // If this reference is talking about some other
                            // mutable, the permission is always false
                            let base_mut_idx = ctx.get_mut_index(base).ok_or(format!("undefined mutable {base}"))?;
                            conditions.push(smt::TermX::eq(mut_idx, smt::TermX::int(base_mut_idx as u64)));
                            break;
                        }
                        MutReferenceX::Deref(..) => unimplemented!("deref in permission"),
                        MutReferenceX::Index(mut_ref, ..) |
                        MutReferenceX::Slice(mut_ref, ..) => {
                            index_ranges.push(rem_mut_ref.clone());
                            rem_mut_ref = mut_ref;
                        },
                    };
                }

                assert!(index_ranges.len() <= indices.len());

                // Want to check that each idx is within the range specified by the outermost slice of mut_ref
                for (idx, mut_ref) in indices.iter().zip(index_ranges.iter().rev()) {
                    match &mut_ref.x {
                        MutReferenceX::Base(..) => unreachable!(),
                        MutReferenceX::Deref(..) => unreachable!(),
                        MutReferenceX::Index(_, t) => {
                            conditions.push(smt::TermX::eq(idx, t.as_smt_term(const_interp, var_interp)?));
                        }
                        MutReferenceX::Slice(_, t1, t2) => {
                            // t1 <= idx
                            if let Some(t1) = t1 {
                                conditions.push(smt::TermX::lte(t1.as_smt_term(const_interp, var_interp)?, idx));
                            }

                            // idx < t2
                            if let Some(t2) = t2 {
                                conditions.push(smt::TermX::lt(idx, t2.as_smt_term(const_interp, var_interp)?));
                            }
                        }
                    }
                }

                Ok(smt::TermX::and(conditions))
            }
        }
    }
}

impl PermJudgment {
    /// Encode the invalidity of the permission judgment as an SMT term
    pub fn encode_invalidity(&self, smt_ctx: &mut EncodingCtx, ctx: &Ctx, num_fractions: u64) -> Result<smt::Term, String> {
        // Set up constant and variable interpretations
        let mut const_interp = IndexMap::new();
        let mut var_interp = IndexMap::new();

        for c in ctx.consts.values() {
            if let Some(sort) = c.typ.as_smt_sort() {
                let fresh_var = smt::TermX::var(smt_ctx.fresh_var(format!("const_{}", &c.name.0), sort));
                const_interp.insert(c.name.clone(), fresh_var);
            } // ignore unsupported sort
        }

        for (v, t) in &self.local.vars {
            if let Some(sort) = t.as_smt_sort() {
                let fresh_var = smt::TermX::var(smt_ctx.fresh_var(format!("var_{}", &v.0), sort));
                var_interp.insert(v.clone(), fresh_var);
            } // ignore unsupported sort
        }

        Ok(smt::TermX::and([
            // Add local constraints
            smt::TermX::and(self.local_constraints.iter()
                .map(|c| c.as_smt_term(&const_interp, &var_interp))
                .collect::<Result<Vec<_>, _>>()?
            ),
            
            // Negation of the permission constraint
            self.perm_constraint.encode_invalidity(smt_ctx, ctx, &const_interp, &var_interp, num_fractions)?
        ]))
    }
}

impl PermConstraintX {
    pub fn less_eq(p1: &Permission, p2: &Permission) -> PermConstraint {
        Rc::new(PermConstraintX::LessEq(p1.clone(), p2.clone()))
    }

    pub fn has_read(m: &MutReference, p: &Permission) -> PermConstraint {
        Rc::new(PermConstraintX::HasRead(m.clone(), p.clone()))
    }

    pub fn has_write(m: &MutReference, p: &Permission) -> PermConstraint {
        Rc::new(PermConstraintX::HasWrite(m.clone(), p.clone()))
    }

    /// Encode the invalidity of the permission constraint to SMT
    /// i.e. if the SMT constraint is unsat, the permission constraint
    /// is valid.
    pub fn encode_invalidity(
        &self,
        smt_ctx: &mut EncodingCtx,
        ctx: &Ctx,

        const_interp: &IndexMap<Const, smt::Term>,
        var_interp: &IndexMap<Var, smt::Term>,
        num_fractions: u64,
    ) -> Result<smt::Term, String> {
        // For all mutable m, and for any indices i_1, ..., i_n of m
        // for any 0 <= j < num_fractions
        // Interpret each permission as a bool
        
        match self {
            PermConstraintX::LessEq(p1, p2) => {
                // Variable for the mutable
                let mut_idx_name = smt_ctx.fresh_var("mut_idx", smt::Sort::Int);
                let frac_idx_name = smt_ctx.fresh_var("frac_idx", smt::Sort::Int);

                let mut_idx = &smt::TermX::var(&mut_idx_name);
                let frac_idx = &smt::TermX::var(&frac_idx_name);

                // Find the largest number of dimensions in any mutable
                let max_dim = ctx.muts.values().map(|decl| decl.typ.get_dimensions()).max().unwrap_or(0);

                // Create max_dim many indices
                let indices: Vec<_> = (0..max_dim)
                    .map(|_| smt::TermX::var(smt_ctx.fresh_var("arr_idx", smt::Sort::Int)))
                    .collect();
                
                // Bound arr_idx >= 0 (and maybe < length of the mutable too?)
                let indices_constraint: Vec<_> = indices.iter()
                    .map(|i| smt::TermX::lte(smt::TermX::int(0), i))
                    .collect();

                // Does there exists a mutable, a fraction index, and indices such that
                // the permission is set at this location for p1 but not for p2
                Ok(smt::TermX::and([
                    // 0 <= mut_idx < |ctx.muts|
                    smt::TermX::lte(smt::TermX::int(0), mut_idx),
                    smt::TermX::lt(mut_idx, smt::TermX::int(ctx.muts.len() as u64)),

                    // 0 <= frac_idx < num_fractions
                    smt::TermX::lte(smt::TermX::int(0), frac_idx),
                    smt::TermX::lt(frac_idx, smt::TermX::int(num_fractions)),

                    smt::TermX::and(indices_constraint),

                    smt::TermX::not(
                        smt::TermX::implies(
                            p1.as_smt_term(ctx, &const_interp, &var_interp, &mut_idx, &indices, &frac_idx)?,
                            p2.as_smt_term(ctx, &const_interp, &var_interp, &mut_idx, &indices, &frac_idx)?,
                        ),
                    ),
                ]))
            }
            PermConstraintX::Disjoint(..) => unimplemented!("disjoint permission constraint"),
            PermConstraintX::HasRead(mut_ref, p) => {
                // has_read(ref, p) <=> read(0) <= p \/ ... \/ read(k - 1) <= p
                let mut conditions = Vec::new();

                for k in 0..num_fractions {
                    conditions.push(Rc::new(PermConstraintX::LessEq(
                        Spanned::new(PermissionX::Fraction(PermFraction::Read(k as u32), mut_ref.clone())),
                        p.clone(),
                    )).encode_invalidity(smt_ctx, ctx, const_interp, var_interp, num_fractions)?);
                }

                Ok(smt::TermX::and(conditions))

                // // forall 0 <= frac_idx < num_fractions. not (read(frac_idx) <= p)
                // Ok(smt::TermX::forall(
                //     [(frac_idx_name, smt::Sort::Int)],
                //     smt::TermX::implies(
                //         // 0 <= frac_idx < num_fractions
                //         smt::TermX::and([
                //             smt::TermX::lte(smt::TermX::int(0), frac_idx),
                //             smt::TermX::lt(frac_idx, smt::TermX::int(num_fractions)),
                //         ]),
                //         smt::TermX::not(
                //             smt::TermX::implies(
                //                 Rc::new(PermissionX::Fraction(PermFraction::Read(k as u32), mut_ref.clone())).as_smt_term(ctx, &const_interp, &var_interp, &mut_idx, &indices, &frac_idx)?,
                //                 p.as_smt_term(ctx, &const_interp, &var_interp, &mut_idx, &indices, &frac_idx)?,
                //             ),
                //         ),
                //     ),
                // ))
            }
            PermConstraintX::HasWrite(mut_ref, p) =>
                Rc::new(PermConstraintX::LessEq(
                    Spanned::new(PermissionX::Fraction(PermFraction::Write, mut_ref.clone())),
                    p.clone(),
                )).encode_invalidity(smt_ctx, ctx, const_interp, var_interp, num_fractions),
        }
    }
}

impl fmt::Display for PermConstraintX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermConstraintX::LessEq(p1, p2) => write!(f, "{} <= {}", p1, p2),
            PermConstraintX::Disjoint(perms) =>
                write!(f, "disjoint({})", perms.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", ")),
            PermConstraintX::HasRead(m, p) => write!(f, "read(*) {} <= {}", m, p),
            PermConstraintX::HasWrite(m, p) => write!(f, "write {} <= {}", m, p),
        }
    }
}
