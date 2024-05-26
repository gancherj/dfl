use std::rc::Rc;
/// AST for permission constraints

/**
 * Semantically, for example,
 * if mut A: [[int]]
 * [write A] := write A[i][j] for all i, j
 * [write A[n..m]] := write A[i][j] for any n <= i < m, and any j
 */
use std::{borrow::Borrow, fmt};

use im::Vector;
use indexmap::IndexMap;

use crate::{
    ast::*,
    check::LocalCtx,
    smt::{self, EncodingCtx, SynthFunGrammar},
    span::{Error, Spanned},
};

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
    pub local_constraints: Vector<Term>,
    pub perm_constraint: PermConstraint,
}

/// Interpretation of constants, local variables
/// and permission variables as background SMT objects
pub struct Interpretation {
    consts: IndexMap<Const, smt::Term>,
    vars: IndexMap<Var, smt::Term>,
    perms: IndexMap<PermVar, smt::Term>,
    mut_idx: smt::Term,
    arr_indices: Vec<smt::Term>,
    frac_idx: smt::Term,

    /// Additional constraints for the free variables
    constraints: Vec<smt::Term>,
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
    pub fn as_smt_sort(&self) -> smt::Sort {
        match self {
            BaseType::Bool => smt::Sort::Bool,
            BaseType::Int => smt::Sort::Int,
        }
    }
}

impl Ctx {
    /// Get the unique index of a mutable
    /// based on the order it is defined
    /// This is used for the SMT encoding of permissions
    fn get_mut_index(&self, name: &MutName) -> Option<usize> {
        return self.muts.get_index_of(name);
    }
}

impl TermX {
    /// Encode the term as an SMT term
    /// All free variables and constants are introduced as SMT constants
    pub fn as_smt_term(term: &Term, interp: &Interpretation) -> Result<smt::Term, Error> {
        match &term.x {
            TermX::Var(v) => interp
                .vars
                .get(v)
                .cloned()
                .ok_or(Error::spanned(term.span, format!("undefined variable {v}"))),
            TermX::Const(c) => interp
                .consts
                .get(c)
                .cloned()
                .ok_or(Error::spanned(term.span, format!("undefined constant {c}"))),
            TermX::Bool(b) => Ok(smt::TermX::bool(*b)),
            TermX::Int(i) => {
                if *i >= 0 {
                    Ok(smt::TermX::int(*i as u64))
                } else {
                    Ok(smt::TermX::neg(smt::TermX::int(-i as u64)))
                }
            }
            TermX::Ref(..) => unimplemented!("reference"),
            TermX::Add(t1, t2) => Ok(smt::TermX::add(
                TermX::as_smt_term(t1, interp)?,
                TermX::as_smt_term(t2, interp)?,
            )),
            TermX::Mul(t1, t2) => Ok(smt::TermX::mul(
                TermX::as_smt_term(t1, interp)?,
                TermX::as_smt_term(t2, interp)?,
            )),
            TermX::And(t1, t2) => Ok(smt::TermX::and([
                TermX::as_smt_term(t1, interp)?,
                TermX::as_smt_term(t2, interp)?,
            ])),
            TermX::Less(t1, t2) => Ok(smt::TermX::lt(
                TermX::as_smt_term(t1, interp)?,
                TermX::as_smt_term(t2, interp)?,
            )),
            TermX::Equal(t1, t2) => Ok(smt::TermX::eq(
                TermX::as_smt_term(t1, interp)?,
                TermX::as_smt_term(t2, interp)?,
            )),
            TermX::Not(t) => Ok(smt::TermX::not(TermX::as_smt_term(t, interp)?)),
        }
    }
}

impl PermissionX {
    /// Encode a permission as an SMT term indicating whether
    /// the permission is true at the given mutable, indices, and fraction index
    ///
    /// In other words, given free variables { x_1, ..., x_n }
    /// a permission is interpreted as a relation
    /// R(x_1, ..., x_n, mut_idx: Int, i_1: Int, ..., i_m: Int, frac_idx: Int): Bool
    /// which is true iff
    /// the permission read(frac_idx) <mut_idx>[i_1]...[i_m] is set
    /// given the values for x_1, ..., x_n
    ///
    /// Some parts of the relation R is not used but we leave them
    /// unconstrained (e.g. if a mutable is only 1-dim, i_2, ..., i_m is not used)
    pub fn as_smt_term(
        perm: &Permission,
        ctx: &Ctx,
        interp: &Interpretation,
    ) -> Result<smt::Term, Error> {
        match &perm.x {
            PermissionX::Empty => Ok(smt::TermX::bool(false)),
            PermissionX::Add(p1, p2) => Ok(smt::TermX::or([
                PermissionX::as_smt_term(p1, ctx, interp)?,
                PermissionX::as_smt_term(p2, ctx, interp)?,
            ])),
            PermissionX::Sub(p1, p2) => Ok(smt::TermX::and([
                PermissionX::as_smt_term(p1, ctx, interp)?,
                smt::TermX::not(PermissionX::as_smt_term(p2, ctx, interp)?),
            ])),
            PermissionX::Ite(t, p1, p2) => Ok(smt::TermX::ite(
                TermX::as_smt_term(t, interp)?,
                PermissionX::as_smt_term(p1, ctx, interp)?,
                PermissionX::as_smt_term(p2, ctx, interp)?,
            )),
            PermissionX::Fraction(frac, mut_ref) => {
                // Conditinos for the permission to be true at the given location
                let mut conditions = Vec::new();

                // If the fraction does not match, the permission is always empty
                if let PermFraction::Write(k) = frac {
                    conditions.push(smt::TermX::ge(&interp.frac_idx, smt::TermX::int(*k as u64)));
                } else if let PermFraction::Read(k) = frac {
                    conditions.push(smt::TermX::eq(&interp.frac_idx, smt::TermX::int(*k as u64)));
                }

                PermissionX::generate_mut_ref_conditions(
                    ctx,
                    interp,
                    mut_ref,
                    &mut conditions,
                    &mut smt::TermX::int(0),
                    &mut 0,
                )?;

                Ok(smt::TermX::and(conditions))
            }
            PermissionX::Var(v, terms) => {
                let encodings = terms
                    .iter()
                    .map(|t| TermX::as_smt_term(t, interp))
                    .collect::<Result<Vec<_>, _>>()?;

                let perm_interp = interp.perms.get(v).ok_or(Error::spanned(
                    perm.span,
                    format!("permission variable `{}` does not exist", v),
                ))?;

                Ok(smt::TermX::app_term(
                    perm_interp,
                    encodings
                        .iter()
                        // .chain(interp.consts.values())
                        // .chain(interp.vars.values())
                        .chain([&interp.mut_idx])
                        .chain(&interp.arr_indices)
                        .chain([&interp.frac_idx]),
                ))
            } // Error::spanned_err(perm.span, format!("permission variable not supported for SMT encoding"))
        }
    }

    /// Generate range conditions on array indices
    /// from a mutable reference
    /// e.g. A[a:b][c][d:e] => a <= idx0 < b /\ idx0 == a + c /\ d <= idx1 < e
    fn generate_mut_ref_conditions(
        ctx: &Ctx,
        interp: &Interpretation,
        mut_ref: &MutReference,
        conditions: &mut Vec<smt::Term>,
        current_base: &mut smt::Term,
        current_idx: &mut usize,
    ) -> Result<(), Error> {
        match &mut_ref.x {
            MutReferenceX::Base(base) => {
                // If this reference is talking about some other
                // mutable, the permission is always false
                let base_mut_idx = ctx.get_mut_index(base).ok_or(Error::spanned(
                    mut_ref.span,
                    format!("undefined mutable {base}"),
                ))?;
                conditions.push(smt::TermX::eq(
                    &interp.mut_idx,
                    smt::TermX::int(base_mut_idx as u64),
                ));

                *current_base = smt::TermX::int(0);
                *current_idx = 0;
            }
            MutReferenceX::Deref(..) => unimplemented!("deref in permission"),
            MutReferenceX::Index(mut_ref, t) => {
                PermissionX::generate_mut_ref_conditions(
                    ctx,
                    interp,
                    mut_ref,
                    conditions,
                    current_base,
                    current_idx,
                )?;

                conditions.push(smt::TermX::eq(
                    &interp.arr_indices[*current_idx],
                    smt::TermX::add(current_base.clone(), TermX::as_smt_term(t, interp)?),
                ));

                // Move on to the next index
                *current_base = smt::TermX::int(0);
                *current_idx += 1;
            }
            MutReferenceX::Slice(mut_ref, t1, t2) => {
                PermissionX::generate_mut_ref_conditions(
                    ctx,
                    interp,
                    mut_ref,
                    conditions,
                    current_base,
                    current_idx,
                )?;

                // t1 <= idx
                if let Some(t1) = t1 {
                    let t1_smt = TermX::as_smt_term(t1, interp)?;
                    conditions.push(smt::TermX::le(&t1_smt, &interp.arr_indices[*current_idx]));
                    *current_base = smt::TermX::add(current_base.clone(), t1_smt);
                }

                // idx < t2
                if let Some(t2) = t2 {
                    conditions.push(smt::TermX::lt(
                        &interp.arr_indices[*current_idx],
                        TermX::as_smt_term(t2, interp)?,
                    ));
                }
            }
        }
        Ok(())
    }
}

pub struct PermInferOptions {
    /// Enable array slices or not
    pub array_slices: bool,

    /// Enable ite in permissions
    pub use_ite: bool,

    /// How many fractions a write can split off
    /// e.g. if num_fractions = 1, we get only one write token
    /// if num_fractions = 2, write = read_1 + read_2
    /// if num_fractions = 0, all permissions are false
    pub num_fractions: usize,
}

impl PermInferOptions {
    pub fn default() -> PermInferOptions {
        PermInferOptions {
            array_slices: false,
            use_ite: false,
            num_fractions: 0,
        }
    }
}

impl Interpretation {
    /// Generate a SyGuS grammar for a permission variable
    fn generate_synthsis_grammar(
        options: &PermInferOptions,
        ctx: &Ctx,
        perm_decl: &PermDecl,
    ) -> SynthFunGrammar {
        let num_arr_idx: usize = ctx.max_mut_dim();

        Rc::new(smt::SynthFunGrammarX {
            symbols: [
                smt::NonTerminal::new("Start", smt::Sort::Bool, [
                    smt::TermX::var("StartAtom"),
                    smt::TermX::or([smt::TermX::var("Start"), smt::TermX::var("StartAtom")]),
                ].into_iter().chain(
                    if options.use_ite {
                        vec![smt::TermX::ite(smt::TermX::var("TermBool"), smt::TermX::var("StartAtom"), smt::TermX::var("StartAtom"))]
                    } else {
                        vec![]
                    }
                )),
                smt::NonTerminal::new("StartAtom", smt::Sort::Bool, [
                    smt::TermX::and(
                        [smt::TermX::var("Mutable")]
                        .into_iter()
                        .chain((0..num_arr_idx).map(|j| smt::TermX::var(format!("ArrayIndex{}", j))))
                        .chain([smt::TermX::var("Fraction")])
                    ),

                    // smt::TermX::or(
                    //     ctx.muts.iter().enumerate().map(|(i, _)| smt::TermX::and(
                    //             [
                    //                 smt::TermX::var("Mutable"),
                    //                 // smt::TermX::var(format!("Mutable{}", i)),
                    //                 // smt::TermX::eq(smt::TermX::var("mut_idx"), smt::TermX::int(i as u64)),
                    //             ]
                    //             .into_iter()
                    //             .chain((0..num_arr_idx).map(|j| smt::TermX::var(format!("ArrayIndex{}", j))))
                    //             .chain([smt::TermX::var("Fraction")])
                    //         ),
                    //     )
                    // ),
                ])
            ].into_iter()
            .chain([
                // ctx.muts.iter().enumerate().map(|(i, _)|
                //     // Three restrict an array index:
                //     // indexing (A[i]), slicing (A[i:] or A[i:j])
                //     smt::NonTerminal::new(format!("Mutable{}", i), smt::Sort::Bool, [
                //         smt::TermX::eq(smt::TermX::var("mut_idx"), smt::TermX::int(i as u64)),
                //     ])
                // )
                smt::NonTerminal::new("Mutable", smt::Sort::Bool, ctx.muts.iter().enumerate().map(|(i, _)|
                    smt::TermX::eq(smt::TermX::var("mut_idx"), smt::TermX::int(i as u64))
                ))
            ])
            .chain(
                (0..num_arr_idx).map(|i|
                    // Two restrict an array index: slicing (A[i:] or A[i:j])
                    if options.array_slices {
                        smt::NonTerminal::new(format!("ArrayIndex{}", i), smt::Sort::Bool, [
                            // smt::TermX::app("arr_index", [smt::TermX::var("TermInt"), smt::TermX::var(format!("arr_idx{}", i))]),
                            smt::TermX::app("arr_from", [smt::TermX::var("TermInt"), smt::TermX::var(format!("arr_idx{}", i))]),
                            smt::TermX::app("arr_range", [smt::TermX::var("TermInt"), smt::TermX::var("TermInt"), smt::TermX::var(format!("arr_idx{}", i))]),
                        ])
                    } else {
                        // No restriction on array indices
                        smt::NonTerminal::new(format!("ArrayIndex{}", i), smt::Sort::Bool, [ smt::TermX::bool(true) ])
                    }
                )
            )
            .chain([
                smt::NonTerminal::new("Fraction", smt::Sort::Bool,
                    // Add all fractions: read(0), read(1), ..., read(num_frac - 2), write(num_frac - 1)
                    (0..options.num_fractions).map(|f|
                        if f == options.num_fractions - 1 {
                            smt::TermX::app("frac_write", [smt::TermX::int(f as u64), smt::TermX::var("frac_idx")])
                        } else {
                            smt::TermX::app("frac_read", [smt::TermX::int(f as u64), smt::TermX::var("frac_idx")])
                        }
                    ).chain(
                        if options.num_fractions == 1 {
                            vec![smt::TermX::bool(false)]
                        } else {
                            vec![
                                smt::TermX::bool(false),
                                smt::TermX::app("frac_write", [smt::TermX::int(0), smt::TermX::var("frac_idx")]),
                            ]
                        }
                    )
                ),
                smt::NonTerminal::new("ConstantInt", smt::Sort::Int, [
                    smt::TermX::int(0),
                    smt::TermX::add(smt::TermX::var("ConstantInt"), smt::TermX::int(1)),
                ]),
                smt::NonTerminal::new("TermInt", smt::Sort::Int,
                    // Only add dependent variables of type int
                    perm_decl.param_typs.iter().enumerate().filter_map(|(i, typ)|
                        match typ {
                            BaseType::Int => Some(smt::TermX::var(format!("x{}", i))),
                            _ => None,
                        }
                    ).chain([
                        smt::TermX::int(0),
                        smt::TermX::add(smt::TermX::var("TermInt"), smt::TermX::int(1)),
                    ]),
                ),
                smt::NonTerminal::new("TermBool", smt::Sort::Bool,
                    // Only add dependent variables of type bool
                    perm_decl.param_typs.iter().enumerate().filter_map(|(i, typ)|
                        match typ {
                            BaseType::Bool => Some(smt::TermX::var(format!("x{}", i))),
                            _ => None,
                        }
                    ).chain([
                        smt::TermX::le(smt::TermX::var("TermInt"), smt::TermX::var("ConstantInt")),
                        // no need for not since we can just reorder ite branches
                        // smt::TermX::not(smt::TermX::var("TermBool")),
                    ]),
                ),
            ]).collect(),
        })
    }

    /// Initialize an interpretation using fresh variables to represent
    /// constants, permission variables, mutable index, etc.
    fn new(
        smt_ctx: &mut EncodingCtx,
        options: &PermInferOptions,
        ctx: &Ctx,
        sygus: bool,
    ) -> Interpretation {
        let mut fresh_universal_var = |prefix, sort| {
            if sygus {
                smt_ctx.fresh_var(prefix, sort)
            } else {
                smt_ctx.fresh_const(prefix, sort)
            }
        };

        let max_dim = ctx.max_mut_dim();
        let mut interp = Interpretation {
            consts: IndexMap::new(),
            vars: IndexMap::new(),
            perms: IndexMap::new(),
            mut_idx: smt::TermX::var(fresh_universal_var("mut_idx".to_string(), smt::Sort::Int)),

            // Create max_dim many indices
            arr_indices: (0..max_dim)
                .map(|_| {
                    smt::TermX::var(fresh_universal_var("arr_idx".to_string(), smt::Sort::Int))
                })
                .collect(),

            frac_idx: smt::TermX::var(fresh_universal_var("frac_idx".to_string(), smt::Sort::Int)),

            constraints: Vec::new(),
        };

        // 0 <= mut_idx < |ctx.muts|
        interp
            .constraints
            .push(smt::TermX::le(smt::TermX::int(0), &interp.mut_idx));
        interp.constraints.push(smt::TermX::lt(
            &interp.mut_idx,
            smt::TermX::int(ctx.muts.len() as u64),
        ));

        // 0 <= frac_idx
        interp
            .constraints
            .push(smt::TermX::le(smt::TermX::int(0), &interp.frac_idx));

        // Set up constraints for array indices
        for arr_idx in &interp.arr_indices {
            interp
                .constraints
                .push(smt::TermX::le(smt::TermX::int(0), arr_idx));
        }

        // Set up constant interpretations
        for decl in ctx.consts.values() {
            let fresh_var = smt::TermX::var(fresh_universal_var(
                format!("const_{}", decl.name.as_str()),
                decl.typ.as_smt_sort(),
            ));
            interp.consts.insert(decl.name.clone(), fresh_var);
        }

        // For SyGuS only, set up permission variable interpretations
        if sygus {
            for decl in ctx.perms.values() {
                // Each permission variable is encoded as a relation
                // R(x_1, ..., x_n, mut_idx: Int, i_1: Int, ..., i_m: Int, frac_idx: Int)
                // where
                // x_1, ..., x_n are dependent parameter types
                // mut_idx is the mutable index
                // i_1, ..., i_m are array indices
                // frac_idx is the fraction index
                let inputs = decl
                    .param_typs
                    .iter()
                    .map(|t| t.as_smt_sort())
                    .enumerate()
                    .map(|(i, t)| (format!("x{}", i), t))
                    .chain([("mut_idx".to_string(), smt::Sort::Int)])
                    .chain((0..max_dim).map(|i| (format!("arr_idx{}", i), smt::Sort::Int)))
                    .chain([("frac_idx".to_string(), smt::Sort::Int)]);

                let fresh_rel = smt_ctx.fresh_synth_fun(
                    format!("pv_{}", decl.name),
                    inputs,
                    smt::Sort::Bool,
                    // None,
                    Some(&Interpretation::generate_synthsis_grammar(
                        options, ctx, decl,
                    )),
                );

                interp
                    .perms
                    .insert(decl.name.clone(), smt::TermX::var(fresh_rel));
            }
        }

        interp
    }
}

impl PermJudgment {
    fn generate_sygus_prelude() -> Vec<smt::Command> {
        vec![
            smt::CommandX::define_fun(
                "arr_index",
                [("i", smt::Sort::Int), ("arr_idx", smt::Sort::Int)],
                smt::Sort::Bool,
                smt::TermX::eq(smt::TermX::var("i"), smt::TermX::var("arr_idx")),
            ),
            smt::CommandX::define_fun(
                "arr_from",
                [("i", smt::Sort::Int), ("arr_idx", smt::Sort::Int)],
                smt::Sort::Bool,
                smt::TermX::le(smt::TermX::var("i"), smt::TermX::var("arr_idx")),
            ),
            smt::CommandX::define_fun(
                "arr_range",
                [
                    ("i", smt::Sort::Int),
                    ("j", smt::Sort::Int),
                    ("arr_idx", smt::Sort::Int),
                ],
                smt::Sort::Bool,
                smt::TermX::and([
                    smt::TermX::le(smt::TermX::var("i"), smt::TermX::var("arr_idx")),
                    smt::TermX::gt(smt::TermX::var("j"), smt::TermX::var("arr_idx")),
                ]),
            ),
            smt::CommandX::define_fun(
                "frac_read",
                [("f", smt::Sort::Int), ("frac_idx", smt::Sort::Int)],
                smt::Sort::Bool,
                smt::TermX::eq(smt::TermX::var("f"), smt::TermX::var("frac_idx")),
            ),
            smt::CommandX::define_fun(
                "frac_write",
                [("f", smt::Sort::Int), ("frac_idx", smt::Sort::Int)],
                smt::Sort::Bool,
                smt::TermX::le(smt::TermX::var("f"), smt::TermX::var("frac_idx")),
            ),
        ]
    }

    /// Encode a list of judgments over permission variables
    /// as a SyGuS query and send it to an SMT solver to solve
    pub fn infer_perm_var(
        judgments: impl IntoIterator<Item = impl Into<PermJudgment>>,
        options: &PermInferOptions,
        ctx: &Ctx,
        solver: &mut smt::Solver,
    ) -> Result<Option<smt::SynthModel>, Error> {
        let mut smt_ctx = EncodingCtx::new("perm");
        let mut smt_constraints = Vec::new();

        let mut interp = Interpretation::new(&mut smt_ctx, options, ctx, true);

        for judgment in judgments {
            smt_constraints.push(judgment.into().encode_validity(
                &mut smt_ctx,
                ctx,
                &mut interp,
                true,
            )?);
        }

        // Send solver commands
        solver
            .push()
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;

        // Send a dummy synth-fun to enable feasibility checking even when there is no
        // permission variable
        let empty_sorts: Vec<(&str, _)> = vec![];
        solver
            .send_command(smt::CommandX::synth_fun(
                "dummy",
                empty_sorts,
                smt::Sort::Bool,
                None,
            ))
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;

        for cmd in PermJudgment::generate_sygus_prelude() {
            solver
                .send_command(cmd)
                .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;
        }

        for cmd in smt_ctx.to_commands() {
            solver
                .send_command(cmd)
                .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;
        }

        for constraint in &interp.constraints {
            solver
                .assume(constraint)
                .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;
        }

        for smt_constraint in smt_constraints {
            solver
                .constraint(smt_constraint)
                .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;
        }

        let result = match solver
            .check_synth()
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?
        {
            smt::CheckSynthResult::Infeasible => Ok(None), // no solution possible
            smt::CheckSynthResult::Fail => Error::new_err(format!("solver failed to synthesize")),
            smt::CheckSynthResult::Synthesized(model) => Ok(Some(model)),
        };

        solver
            .pop()
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;

        result
    }

    // Check the validity of a single judgments with no permission variables
    pub fn check_validity(&self, ctx: &Ctx, solver: &mut smt::Solver) -> Result<bool, Error> {
        let mut smt_ctx = EncodingCtx::new("perm");
        let mut interp =
            Interpretation::new(&mut smt_ctx, &PermInferOptions::default(), ctx, false);

        let validity = self.encode_validity(&mut smt_ctx, ctx, &mut interp, false)?;

        // Send solver commands
        solver
            .push()
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;

        for cmd in smt_ctx.to_commands() {
            solver
                .send_command(cmd)
                .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;
        }

        for constraint in interp.constraints {
            solver
                .assert(constraint)
                .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;
        }

        solver
            .assert(smt::TermX::not(validity))
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;

        let result = match solver
            .check_sat()
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?
        {
            smt::CheckSatResult::Sat => Ok(false),
            smt::CheckSatResult::Unsat => Ok(true),
            smt::CheckSatResult::Unknown => Error::new_err(format!("solver returned unknown")),
        };

        solver
            .pop()
            .map_err(|msg| Error::new(format!("solver error: {}", msg)))?;

        result
    }

    /// Encode validity of the judgment either as an SMT query
    /// or an SyGuS query
    /// For SMT query (sygus = false), the judgment is valid iff output is unsat
    /// For SyGuS query, the judgment is valid iff output is feasible
    pub fn encode_validity(
        &self,
        smt_ctx: &mut EncodingCtx,
        ctx: &Ctx,
        interp: &mut Interpretation,
        sygus: bool,
    ) -> Result<smt::Term, Error> {
        // In an SMT query, (negated) universal variables are skolemized as constants;
        // in a SyGuS query, universal variables are declared using (declare-var ...)
        let mut fresh_universal_var = |prefix, sort| {
            if sygus {
                smt_ctx.fresh_var(prefix, sort)
            } else {
                smt_ctx.fresh_const(prefix, sort)
            }
        };

        // Only local variables need to be rebinded
        interp.vars.clear();
        for (v, t) in &self.local.vars {
            if let TermTypeX::Base(t) = t.borrow() {
                let fresh_var = smt::TermX::var(fresh_universal_var(
                    format!("var_{}", v.as_str()),
                    t.as_smt_sort(),
                ));
                interp.vars.insert(v.clone(), fresh_var);
            } // ignore unsupported sort
        }

        let validity = smt::TermX::implies(
            // Add local constraints (path conditions)
            smt::TermX::and(
                self.local_constraints
                    .iter()
                    .map(|c| TermX::as_smt_term(c, &interp))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            self.perm_constraint.as_smt_term(smt_ctx, ctx, &interp)?,
        );

        Ok(validity)
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
    pub fn as_smt_term(
        &self,
        smt_ctx: &mut EncodingCtx,
        ctx: &Ctx,
        interp: &Interpretation,
    ) -> Result<smt::Term, Error> {
        match self {
            PermConstraintX::LessEq(p1, p2) => {
                // Does there exists a mutable, a fraction index, and indices such that
                // the permission is set at this location for p1 but not for p2
                Ok(smt::TermX::implies(
                    PermissionX::as_smt_term(p1, ctx, interp)?,
                    PermissionX::as_smt_term(p2, ctx, interp)?,
                ))
            }
            PermConstraintX::Disjoint(..) => unimplemented!("disjoint permission constraint"),
            PermConstraintX::HasRead(mut_ref, p) => {
                // has_read(ref, p)
                // iff read(0) <= p \/ ... \/ read(k - 1) <= p
                // iff exists frac_idx. read(frac_idx) <= p

                // let mut conditions = Vec::new();

                // for k in 0..num_fractions {
                //     conditions.push(Rc::new(PermConstraintX::LessEq(
                //         Spanned::new(PermissionX::Fraction(PermFraction::Read(k as u32), mut_ref.clone())),
                //         p.clone(),
                //     )).as_smt_term(smt_ctx, ctx, interp, &mut_idx, &indices, &frac_idx, num_fractions)?);
                // }

                // Ok(smt::TermX::and(conditions))

                let frac_idx_name = &smt_ctx.fresh_ident("frac_idx");
                let frac_idx = &smt::TermX::var(frac_idx_name);

                Ok(smt::TermX::forall(
                    [(frac_idx_name, smt::Sort::Int)],
                    smt::TermX::implies(
                        // 0 <= frac_idx
                        smt::TermX::le(smt::TermX::int(0), frac_idx),
                        Rc::new(PermConstraintX::LessEq(
                            // NOTE: using ::Write here is intensional
                            Spanned::new(PermissionX::Fraction(
                                PermFraction::Write(0),
                                mut_ref.clone(),
                            )),
                            p.clone(),
                        ))
                        .as_smt_term(smt_ctx, ctx, interp)?,
                    ),
                ))
            }
            PermConstraintX::HasWrite(mut_ref, p) => Rc::new(PermConstraintX::LessEq(
                Spanned::new(PermissionX::Fraction(
                    PermFraction::Write(0),
                    mut_ref.clone(),
                )),
                p.clone(),
            ))
            .as_smt_term(smt_ctx, ctx, interp),
        }
    }
}

impl fmt::Display for PermConstraintX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermConstraintX::LessEq(p1, p2) => write!(f, "{} <= {}", p1, p2),
            PermConstraintX::Disjoint(perms) => write!(
                f,
                "disjoint({})",
                perms
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            PermConstraintX::HasRead(m, p) => write!(f, "read(*) {} <= {}", m, p),
            PermConstraintX::HasWrite(m, p) => write!(f, "write(0) {} <= {}", m, p),
        }
    }
}
