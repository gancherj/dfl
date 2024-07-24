use core::fmt;
use std::collections::HashSet;
use std::hash::Hash;
use std::rc::Rc;

use im::Vector;
use indexmap::{IndexMap, IndexSet};
use std::collections::HashMap;

use crate::ast::*;
use crate::error::Error;
use crate::execution::*;
use crate::smt;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
/**
 * Shape is an equivalence class of configurations
 * that share the same number of values in each channel
 */
struct Shape {
    chans: Vec<usize>,
    procs: Vec<Option<ProcName>>, // Some if the process is alive, otherwise None
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

    shape_indices: HashMap<Rc<Shape>, ShapeIndex>,
    index_to_shape: Vec<Rc<Shape>>,
    changed_shapes: IndexSet<ShapeIndex>,

    // All reachable shapes
    shapes: HashMap<ShapeIndex, ShapeAbstraction>,
}

pub struct Subsumption {
    pub subst: im::HashMap<smt::Ident, smt::Term>,
    pub condition: Vec<smt::Term>,
}

/**
 * In a configuration, a process P has a wait dependency on Q if
 * In the current config, P blocks on recv (send) a channel C,
 * and the send (recv) ownership of C is held by Q
 *
 * Since P may branch, the each wait dependency edge is
 * conditioned by a path condition wrt variables in the config.
 */
pub struct WaitDependencyGraph {
    // [ src -> [ dest -> condition1 \/ condition2 ] ]
    // NOTE: the conditions are disjunctive
    edges: IndexMap<ProcName, IndexMap<ProcName, Vec<smt::Term>>>,
}

impl Configuration {
    fn get_shape(&self) -> Result<Shape, String> {
        let chans = self
            .ctx
            .chans
            .values()
            .map(|decl| self.chans.get(&decl.name).map(|s| s.len()))
            .collect::<Option<_>>()
            .ok_or(format!("channel not found"))?;
        let procs = self
            .procs
            .iter()
            .map(|s| match s {
                ProcState::Call(name, _) => Some(name.clone()),
                ProcState::End => None,
            })
            .collect();

        Ok(Shape { chans, procs })
    }

    /// Build a wait dependency graph from the configuration
    fn build_wait_dep_graph(&self) -> Result<WaitDependencyGraph, Error> {
        let mut edges = IndexMap::new();

        // c -> owner of `input c`
        let mut in_chan_owners = IndexMap::new();

        // c -> owner of `output c`
        let mut out_chan_owners = IndexMap::new();

        // Map channels to their owners
        for proc_state in &self.procs {
            match proc_state {
                ProcState::End => {}
                ProcState::Call(proc_name, ..) => {
                    let decl = self
                        .ctx
                        .procs
                        .get(proc_name)
                        .ok_or(format!("undefined process"))?;
                    for res in &decl.res {
                        match &res.x {
                            ProcResourceX::Perm(..) => {}
                            ProcResourceX::Input(name) => {
                                in_chan_owners.insert(name.clone(), proc_name.clone());
                            }
                            ProcResourceX::Output(name) => {
                                out_chan_owners.insert(name.clone(), proc_name.clone());
                            }
                        }
                    }
                }
            }
        }

        // Iterate through each process state and gather their dependencies
        for proc_state in &self.procs {
            let mut out_edges: IndexMap<_, Vec<smt::Term>> = IndexMap::new();

            if let ProcState::Call(proc_name, ..) = proc_state {
                let results = self.eval_proc_state(proc_state)?;
                assert!(results.len() > 0);

                for result in results {
                    match result {
                        ProcEvalResult::Full(..) => {} // not stuck, no dependency
                        ProcEvalResult::Partial(rem, _, path_conditions) => {
                            let owner = match &rem.x {
                                // Blocked on send, want to find the owner of input of the channel
                                ProcX::Send(chan, ..) => in_chan_owners.get(chan),
                                ProcX::Recv(chan, ..) => out_chan_owners.get(chan),
                                _ => unreachable!("blocked at non-blockable process"),
                            };

                            // If the owner is live, add the dependency (extend the path conditions if the dependency exists)
                            if let Some(owner) = owner {
                                if out_edges.contains_key(owner) {
                                    out_edges
                                        .get_mut(owner)
                                        .unwrap()
                                        .push(smt::TermX::and(path_conditions));
                                } else {
                                    out_edges.insert(
                                        owner.clone(),
                                        vec![smt::TermX::and(path_conditions)],
                                    );
                                }
                            }
                        }
                    }
                }

                // Add out edges for proc_name
                edges.insert(proc_name.clone(), out_edges);
            }
        }

        Ok(WaitDependencyGraph { edges })
    }

    /// Get the first non-skip process state
    fn get_first_live_process(&self) -> Option<&ProcName> {
        for proc_state in &self.procs {
            if let ProcState::Call(proc_name, ..) = proc_state {
                return Some(proc_name);
            }
        }
        None
    }

    /**
     * Given a (symbolic) configuration, check if there
     * is a wait cycle between processes
     *
     * If so, return the processes involved in the cycle.
     * Otherwise return empty vector
     */
    fn find_wait_cycle(&self, solver: &mut smt::Solver) -> Result<Option<Vec<ProcName>>, Error> {
        let wait_dep = self.build_wait_dep_graph()?;

        // Find a cycle (with satisfiable path conditions) using dfs
        let mut stack = Vector::new();

        let mut visited = HashSet::new(); // visited nodes with no cycles
        let mut ancestor = IndexSet::new(); // ancestors for the current node

        // Get the first non-skip process state
        if let Some(name) = self.get_first_live_process() {
            stack.push_back(name);
        } else {
            // No live processes, so no possible cycles
            return Ok(None);
        }

        loop {
            if let Some(proc_name) = stack.pop_back() {
                if ancestor.contains(proc_name) {
                    assert!(ancestor.last() == Some(&proc_name));
                    ancestor.shift_remove(proc_name);
                    visited.insert(proc_name);
                    continue;
                } else {
                    ancestor.insert(proc_name);
                    // visit the node again to remove ancestor tag
                    // once all children are visited
                    stack.push_back(proc_name);
                }

                // If any children points to an ancestor node, we found a cycle
                if let Some(out_edges) = wait_dep.edges.get(proc_name) {
                    for (child, conditions) in out_edges.iter() {
                        if let Some(ancestor_idx) = ancestor.get_index_of(child) {
                            // Found a cycle
                            // Check if the path condition from the ancestor all the way down is satisfiable
                            let mut path_conditions = vec![smt::TermX::or(conditions)];

                            // For each two adjacent ancestor from ancestor idx
                            // Collect the path condition between them
                            for (ancestor1, ancestor2) in ancestor
                                .iter()
                                .skip(ancestor_idx)
                                .zip(ancestor.iter().skip(ancestor_idx + 1))
                            {
                                let conditions = wait_dep
                                    .edges
                                    .get(*ancestor1)
                                    .unwrap()
                                    .get(*ancestor2)
                                    .unwrap();
                                path_conditions.push(smt::TermX::or(conditions));
                            }

                            // Solve the path conditions for satisfiability
                            solver.push()?;
                            for condition in self.path_conditions.iter() {
                                solver.assert(condition)?;
                            }
                            let result = solver.check_sat()?;
                            solver.pop()?;

                            if result == smt::CheckSatResult::Sat {
                                // Found a feasible cycle
                                return Ok(Some(
                                    ancestor
                                        .iter()
                                        .skip(ancestor_idx)
                                        .map(|p| (*p).clone())
                                        .collect(),
                                ));
                            }
                            // Otherwise, we found a infeasible cycle
                            println!("infeasible cycle")
                        } else {
                            stack.push_back(child);
                        }
                    }
                }
            } else {
                break;
            }
        }

        Ok(None)
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
        let mut match_terms =
            |self_term: &smt::Term, other_term: &smt::Term| -> Result<(), Error> {
                let var = self_term
                    .as_var()
                    .ok_or(format!("expecting variable on the pattern side"))?;
                assert!(
                    !subst.contains_key(&var),
                    "duplicate variable {} in the pattern",
                    &var
                );
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
            match (self_proc, other_proc) {
                (
                    ProcState::Call(self_name, self_args),
                    ProcState::Call(other_name, other_args),
                ) if self_name == other_name => {
                    for (self_term, other_term) in self_args.iter().zip(other_args.iter()) {
                        match_terms(self_term, other_term)?;
                    }
                }
                (ProcState::End, ProcState::End) => {}
                _ => return Ok(None),
            }
        }

        // Substitute the path condition
        let condition = self
            .path_conditions
            .iter()
            .map(|term| smt::TermX::substitute(term, &subst))
            .collect();

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
     *
     * Assume all new_configs are feasible configurations
     */
    fn extend(
        &mut self,
        smt_ctx: &mut smt::EncodingCtx,
        solver: &mut smt::Solver,
        mut new_configs: Vec<Configuration>,
    ) -> Result<bool, Error> {
        // 1. Filter out infeasible new configs (|new_configs| queries)
        // 2. Learn (x == c) predicates at each variable (|size of shape| queries)
        // 3. Syntactically learn equalities between variables (0 queries)
        //    (incomplete, but still monotone)

        if let Some(first_config) = new_configs.first() {
            // If there are any feasible configurations, continue

            // Naive version: do not learn constraints on the variables
            if self.pattern.is_none() {
                let ctx = first_config.ctx.clone();
                let mut muts = im::HashMap::new();
                let mut chans = im::HashMap::new();
                let mut procs = Vector::new();

                for decl in ctx.muts.values() {
                    let ident = smt_ctx
                        .fresh_const(format!("shape_mut_{}", decl.name), decl.typ.as_smt_sort());
                    muts.insert(decl.name.clone(), smt::TermX::var(ident));
                }

                for (i, decl) in ctx.chans.values().enumerate() {
                    let bound = first_config.chans[&decl.name].bound;
                    let mut state = ChanState::new(bound);

                    // Generate placeholders for each channel value
                    for j in 0..self.shape.chans[i] {
                        let ident = smt_ctx.fresh_const(
                            format!("shape_chan_{}_{}", decl.name, j),
                            decl.typ.as_smt_sort(),
                        );
                        state.push(smt::TermX::var(ident));
                    }

                    chans.insert(decl.name.clone(), state);
                }

                for proc in &first_config.procs {
                    match proc {
                        ProcState::Call(name, _) => {
                            let decl = ctx.procs.get(name).ok_or(format!("undefined process"))?;
                            // Generate fresh variables for each process parameter
                            let args = decl
                                .params
                                .iter()
                                .map(|param| {
                                    let ident = smt_ctx.fresh_const(
                                        format!("shape_proc_param_{}", param.name),
                                        param.typ.as_smt_sort(),
                                    );
                                    smt::TermX::var(ident)
                                })
                                .collect();
                            procs.push_back(ProcState::Call(name.clone(), args));
                        }
                        ProcState::End => procs.push_back(ProcState::End),
                    }
                }

                self.pattern = Some(Configuration {
                    muts,
                    chans,
                    procs,
                    path_conditions: Vector::new(),
                    ..new_configs.remove(0)
                });

                smt_ctx.flush(solver)?;

                return Ok(true);
            }
        }

        return Ok(false);
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
            shape_indices: HashMap::new(),
            index_to_shape: Vec::new(),
            changed_shapes: IndexSet::new(),
            shapes: HashMap::new(),
        }
    }

    /**
     * Look up the index of a shape.
     * If not found, create a new index
     */
    fn get_shape_index(&mut self, config: &Configuration) -> Result<ShapeIndex, Error> {
        let shape = Rc::new(config.get_shape()?);
        match self.shape_indices.get(&shape) {
            Some(idx) => Ok(*idx),
            None => {
                let idx = self.shape_indices.len();
                self.shape_indices.insert(shape.clone(), idx);
                self.index_to_shape.push(shape);
                Ok(idx)
            }
        }
    }

    /**
     * Assuming all configs have the same shape and are feasible
     *
     * Add the configurations to their shape abstraction
     * If the abstraction changed due to the new examples
     * update changed_shape
     */
    fn extend_shape(
        &mut self,
        solver: &mut smt::Solver,
        shape_idx: ShapeIndex,
        configs: Vec<Configuration>,
    ) -> Result<(), Error> {
        if !self.shapes.contains_key(&shape_idx) {
            self.shapes.insert(
                shape_idx,
                ShapeAbstraction::new(&self.index_to_shape[shape_idx]),
            );
        }

        let abs = self.shapes.get_mut(&shape_idx).unwrap();
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
    pub fn compute_reachable_shapes(
        &mut self,
        solver: &mut smt::Solver,
        entry: impl Into<ProcName>,
        chan_bound: usize,
    ) -> Result<(), Error> {
        // Add the initial configuration
        let init_config = Configuration::new(&mut self.smt_ctx, &self.ctx, entry, chan_bound)?;
        let init_shape_idx = self.get_shape_index(&init_config)?;
        self.extend_shape(solver, init_shape_idx, vec![init_config])?;

        // Iterate until no more changes in the shape abstraction
        while self.changed_shapes.len() > 0 {
            println!(
                "all shapes: {}, changed shapes: {}",
                self.shapes.len(),
                self.changed_shapes.len()
            );

            // Pop all changed shapes
            let old_changed_shapes = self.changed_shapes.iter().cloned().collect::<Vec<_>>();
            self.changed_shapes.clear();

            let mut new_configs = IndexMap::new();

            // Step all changed shapes to get new configurations
            for shape_idx in old_changed_shapes {
                // Get the abstraction pattern
                let abs_pattern = self
                    .shapes
                    .get(&shape_idx)
                    .unwrap()
                    .pattern
                    .as_ref()
                    .unwrap();

                // Make one step
                for result in abs_pattern.step_one_proc()? {
                    match result {
                        StepResult::Step(_, new_config) => {
                            self.smt_ctx.flush(solver)?;
                            if new_config.feasible(solver)? == smt::CheckSatResult::Sat {
                                // Found a feasible step
                                let shape_idx = self.get_shape_index(&new_config)?;

                                if !new_configs.contains_key(&shape_idx) {
                                    new_configs.insert(shape_idx, Vec::new());
                                }
                                new_configs.get_mut(&shape_idx).unwrap().push(new_config);
                            }
                        }
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

    /// Check if any shape abstraction has a wait cycle
    pub fn find_wait_cycle(
        &mut self,
        solver: &mut smt::Solver,
    ) -> Result<Option<Vec<ProcName>>, Error> {
        self.smt_ctx.flush(solver)?;
        for shape_abs in self.shapes.values() {
            if let Some(pattern) = &shape_abs.pattern {
                let cycle = pattern.find_wait_cycle(solver)?;
                if cycle.is_some() {
                    println!("cycle in shape: {}", shape_abs);

                    return Ok(cycle);
                }
            }
        }
        Ok(None)
    }
}

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Shape([{}], [{}])",
            self.chans
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.procs
                .iter()
                .map(|i| match i {
                    Some(name) => format!("{}(..)", name),
                    None => "skip".to_string(),
                })
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

impl fmt::Display for ShapeAbstraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.pattern {
            Some(pattern) => write!(f, "ShapeAbstraction({}, {})", self.shape, pattern),
            None => write!(f, "ShapeAbstraction({}, empty)", self.shape),
        }
    }
}
