/// AST for permission constraints

use std::fmt;
use std::rc::Rc;

use crate::ast::*;

pub type PermConstraint = Rc<PermConstraintX>;
#[derive(Debug)]
pub enum PermConstraintX {
    LessEq(Permission, Permission),
    Disjoint(Vec<Permission>),
    HasRead(MutReference, Permission),
    HasWrite(MutReference, Permission),
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
}

impl fmt::Display for PermConstraintX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermConstraintX::LessEq(p1, p2) => write!(f, "{} <= {}", p1, p2),
            PermConstraintX::Disjoint(perms) =>
                write!(f, "disjoint({})", perms.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", ")),
            PermConstraintX::HasRead(m, p) => write!(f, "write {} <= {}", m, p),
            PermConstraintX::HasWrite(m, p) => write!(f, "read {} <= {}", m, p),
        }
    }
}
