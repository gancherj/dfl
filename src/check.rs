use indexmap::IndexMap;

use crate::ast::*;

/**
 * Type checking:
 * 1. Term is well-typed
 * 2. Permission is well-typed
 * 3. Process is well-typed in channel usage
 * 4. Process is well-typed in permissions (requires SMT)
 */

pub struct LocalCtx {
    pub var_typs: IndexMap<Var, BaseType>,
}

pub struct PermCtx {
    pub perm: Permission,
}

// impl TermX {
//     pub fn type_check(&self) -> Result<(), String> {

//     }
// }
