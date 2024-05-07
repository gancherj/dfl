/// AST for permission constraints
use std::rc::Rc;

use crate::ast::*;

pub type PermConstraint = Rc<PermConstraintX>;
pub enum PermConstraintX {
    LessEq(Permission, Permission),
    Disjoint(Vec<Permission>),
    HasRead(MutReference, Permission),
    HasWrite(MutReference, Permission),
}
