use core::fmt;
use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;

use std::collections::HashMap;
use im::{Vector, vector};
use indexmap::{IndexMap, IndexSet};

use crate::ast::*;
use crate::execution::*;
use crate::smt;
use crate::error::Error;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
/**
 * Shape is an equivalence class of configurations
 * that share the same number of values in each channel
 */
struct Shape {
    chans: Vec<usize>,
    procs: Vec<ProcName>,
}

type ShapeIndex = usize;

struct ShapeAbstraction {
    shape: Rc<Shape>,
    pattern: Option<Configuration>,
    examples: Vec<Configuration>,
}

pub struct ModelChecker {
    ctx: Rc<Ctx>,
    smt_ctx: smt::EncodingCtx,

    shapes: HashMap<Rc<Shape>, ShapeIndex>,
    index_to_shape: Vec<Rc<Shape>>,
    changed_shapes: IndexSet<ShapeIndex>,

    abs: HashMap<ShapeIndex, ShapeAbstraction>,
}

pub struct Subsumption {
    pub subst: im::HashMap<smt::Ident, smt::Term>,
    pub condition: Vec<smt::Term>,
}

impl Configuration {
    fn get_shape(&self) -> Result<Shape, String> {
        let chans = self.ctx.chans.values()
            .map(|decl| self.chans.get(&decl.name).map(|s| s.len()))
            .collect::<Option<_>>()
            .ok_or(format!("channel not found"))?;
        let procs = self.procs.iter().map(|s| s.name.clone()).collect();

        Ok(Shape { chans, procs })
    }

    /**
     * Check if self subsumes the given config via syntactical matching
     * For this to be complete, self must only have distinct variables in it.
     * No expressions or constants are allowed in the configuration (except for the path condition)
     */
    fn subsume(&self, config: &Configuration) -> Result<Option<Subsumption>, Error> {
        let mut subst = im::HashMap::new();

        // A helper function to match up a variable in the pattern with the other term
        // and collect the mapping to the substitution
        let mut match_terms = |self_term: &smt::Term, other_term: &smt::Term| -> Result<(), Error> {
            let var = self_term.as_var().ok_or(format!("expecting variable on the pattern side"))?;
            assert!(!subst.contains_key(&var), "duplicate variable {} in the pattern", &var);
            subst.insert(var, other_term.clone());
            Ok(())
        };

        // Match mutable states
        for name in self.ctx.muts.keys() {
            let self_term = self.muts.get(name).ok_or(format!("undefined mutable"))?;
            let other_term = config.muts.get(name).ok_or(format!("undefined mutable"))?;
            match_terms(self_term, other_term)?;
        }

        // Match channel states
        for name in self.ctx.chans.keys() {
            let self_state = self.chans.get(name).ok_or(format!("undefined channel"))?;
            let other_state = config.chans.get(name).ok_or(format!("undefined channel"))?;

            if self_state.len() != other_state.len() {
                return Ok(None);
            }

            for (self_term, other_term) in self_state.values().zip(other_state.values()) {
                match_terms(self_term, other_term)?;
            }
        }

        // Match process states
        if self.procs.len() != config.procs.len() {
            return Ok(None);
        }

        for (self_proc, other_proc) in self.procs.iter().zip(config.procs.iter()) {
            if self_proc.name != other_proc.name {
                return Ok(None);
            }

            for (self_term, other_term) in self_proc.args.iter().zip(other_proc.args.iter()) {
                match_terms(self_term, other_term)?;
            }
        }

        // Substitute the path condition
        let condition = self.path_conditions.iter().map(|term| smt::TermX::substitute(term, &subst)).collect();

        Ok(Some(Subsumption { subst, condition }))
    }
}

impl ShapeAbstraction {
    fn new(shape: &Rc<Shape>) -> ShapeAbstraction {
        ShapeAbstraction {
            shape: shape.clone(),
            pattern: None,
            examples: Vec::new(),
        }
    }

    /**
     * Extend an abstraction with more examples
     * Return true iff the abstraction needs to be weakened
     */
    fn extend(&mut self, smt_ctx: &mut smt::EncodingCtx, solver: &mut smt::Solver, mut new_configs: Vec<Configuration>) -> Result<bool, Error> {
        // 1. Filter out infeasible new configs (|new_configs| queries)
        // 2. Learn (x == c) predicates at each variable (|size of shape| queries)
        // 3. Syntactically learn equalities between variables (0 queries)
        //    (incomplete, but still monotone)

        // Naive version
        if self.pattern.is_none() {
            let ctx = new_configs[0].ctx.clone();
            let mut muts = im::HashMap::new();
            let mut chans = im::HashMap::new();
            let mut procs = Vector::new();

            for decl in ctx.muts.values() {
                let ident = smt_ctx.fresh_const(format!("shape_mut_{}", decl.name), decl.typ.as_smt_sort());
                muts.insert(decl.name.clone(), smt::TermX::var(ident));
            }

            for (i, decl) in ctx.chans.values().enumerate() {
                let bound = new_configs[0].chans[&decl.name].bound;
                let mut state = ChanState::new(bound);

                // Generate placeholders for each channel value
                for j in 0..self.shape.chans[i] {
                    let ident = smt_ctx.fresh_const(format!("shape_chan_{}_{}", decl.name, j), decl.typ.as_smt_sort());
                    state.push(smt::TermX::var(ident));
                }

                chans.insert(decl.name.clone(), state);
            }

            for proc in &new_configs[0].procs {
                let decl = ctx.procs.get(&proc.name).ok_or(format!("undefined process"))?;
                // Generate fresh variables for each process parameter
                let args = decl.params.iter()
                    .map(|param| {
                        let ident = smt_ctx.fresh_const(format!("shape_proc_param_{}", param.name), param.typ.as_smt_sort());
                        smt::TermX::var(ident)
                    })
                    .collect();
                procs.push_back(ProcState { name: proc.name.clone(), args });
            }

            self.pattern = Some(Configuration {
                muts,
                chans,
                procs,
                path_conditions: Vector::new(),
                ..new_configs.remove(0)
            });

            Ok(true)
        } else {
            Ok(false)
        }
    }
}

/**
 * The initial abstraction uses these predicates:
 * 1. The number of values in each channel
 * 2. The state of each process
 * 3. x == c for some constant c
 * 4. x == y for any two variables
 *
 * We need:
 * 1. Merge an abstraction with a set of symbolic configurations
 * 2. Check if a symbolic configuration is subsumed by an abstraction
 */
impl ModelChecker {
    pub fn new(ctx: &Rc<Ctx>) -> ModelChecker {
        ModelChecker {
            ctx: ctx.clone(),
            smt_ctx: smt::EncodingCtx::new("mc"),
            shapes: HashMap::new(),
            index_to_shape: Vec::new(),
            changed_shapes: IndexSet::new(),
            abs: HashMap::new(),
        }
    }

    /**
     * Look up the index of a shape.
     * If not found, create a new index
     */
    fn get_shape_index(&mut self, config: &Configuration) -> Result<ShapeIndex, Error> {
        let shape = Rc::new(config.get_shape()?);
        match self.shapes.get(&shape) {
            Some(idx) => Ok(*idx),
            None => {
                let idx = self.shapes.len();
                self.shapes.insert(shape.clone(), idx);
                self.index_to_shape.push(shape);
                Ok(idx)
            }
        }
    }

    /**
     * Assuming all configs have the same shape
     *
     * Add the configurations to their shape abstraction
     * If the abstraction changed due to the new examples
     * update changed_shape
     */
    fn extend_shape(&mut self, solver: &mut smt::Solver, shape_idx: ShapeIndex, configs: Vec<Configuration>) -> Result<(), Error> {
        if !self.abs.contains_key(&shape_idx) {
            self.abs.insert(shape_idx, ShapeAbstraction::new(&self.index_to_shape[shape_idx]));
        }

        let abs = self.abs.get_mut(&shape_idx).unwrap();
        if abs.extend(&mut self.smt_ctx, solver, configs)? {
            // Shape abstraction changed
            self.changed_shapes.insert(shape_idx);

            println!("changed shape: {}", abs);
        }

        Ok(())
    }

    /**
     * Initialize the shape abstraction based on the context
     */
    pub fn abstract_shape(&mut self, solver: &mut smt::Solver, entry: impl Into<ProcName>, chan_bound: usize) -> Result<(), Error> {
        // Add the initial configuration
        let init_config = Configuration::new(&mut self.smt_ctx, &self.ctx, entry, chan_bound)?;
        let init_shape_idx = self.get_shape_index(&init_config)?;
        self.extend_shape(solver, init_shape_idx, vec![init_config])?;

        // Iterate until no more changes in the shape abstraction
        while self.changed_shapes.len() > 0 {
            println!("all shapes: {}, changed shapes: {}", self.abs.len(), self.changed_shapes.len());

            // Pop all changed shapes
            let old_changed_shapes = self.changed_shapes.iter().cloned().collect::<Vec<_>>();
            self.changed_shapes.clear();

            let mut new_configs = IndexMap::new();

            // Step all changed shapes to get new configurations
            for shape_idx in old_changed_shapes {
                // Get the abstraction pattern
                let abs_pattern = self.abs.get(&shape_idx).unwrap().pattern.as_ref().unwrap();

                // Make one step
                for result in abs_pattern.step_one_proc()? {
                    match result {
                        StepResult::Step(_, new_config) => {
                            let shape_idx = self.get_shape_index(&new_config)?;

                            if !new_configs.contains_key(&shape_idx) {
                                new_configs.insert(shape_idx, Vec::new());
                            }
                            new_configs.get_mut(&shape_idx).unwrap().push(new_config);
                        },
                        StepResult::Terminal(..) => {} // ignore terminal branches
                    }
                }
            }

            // Add new configurations to the shape abstraction
            for (shape_idx, configs) in new_configs {
                self.extend_shape(solver, shape_idx, configs)?;
            }
        }

        Ok(())
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Shape([{}], [{}])",
            self.chans.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(", "),
            self.procs.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(", "),
        )
    }
}

impl fmt::Display for ShapeAbstraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ShapeAbstraction({})", self.shape)
    }
}
