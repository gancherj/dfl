#![allow(unused_imports)]
#![allow(dead_code)]
use crate::ast::*;
use fraction::{Fraction, One, Zero};
use im::hashmap;
use im::hashmap::*;
use im::hashset::*;
use std::rc::Rc;
use crate::check::Ctx;

impl Permission {
    pub fn valid(&self, ctx : &Ctx) -> bool {
        self.0.keys().all(|k| ctx.locations.contains_key(k))
    }

    pub fn empty() -> Permission {
        Permission(HashMap::new())
    }

    pub fn is_empty(&self) -> bool {
        let mut b = true;
        for (_, f) in &self.0 {
            if *f > Fraction::one() {
                b = false;
            }
        }
        b
    }

    pub fn nonnegative(&self) -> bool {
        let mut b = true;
        for (_, f) in &self.0 {
            if *f < Fraction::zero() {
                b = false;
            }
        }
        b
    }

    pub fn singleton(l: &Location, f: Option<Fraction>) -> Permission {
        Permission(hashmap! { l.clone() => f.unwrap_or(Fraction::one()) })
    }

    pub fn contains_write(&self, l: &Location) -> bool {
        match self.0.get(l) {
            None => false,
            Some(f) => *f >= Fraction::new(1u64, 1u64),
        }
    }

    pub fn contains_read(&self, l: &Location) -> bool {
        match self.0.get(l) {
            None => false,
            Some(f) => *f > Fraction::new(0u64, 1u64),
        }
    }

    pub fn add(&self, other: &Permission) -> Permission {
        let mut p = self.0.clone();
        for (k, v) in &other.0 {
            p = p.alter(
                |ov| {
                    let v1 = ov.unwrap_or(Fraction::zero());
                    Some(v1 + *v)
                },
                k.clone(),
            )
        }
        Permission(p)
    }

    pub fn subtract(&self, other: &Permission) -> Result<Permission, String> {
        let mut fail = false;
        let mut p = self.0.clone();
        for (k, v2) in &other.0 {
            p = p.alter(
                |ov| {
                    let v1 = ov.unwrap_or(Fraction::zero());
                    if (v1 - *v2) >= Fraction::zero() {
                        Some(v1 - *v2)
                    } else {
                        fail = true;
                        None
                    }
                },
                k.clone(),
            )
        }
        if fail {
            Err("Permission subtract failure".to_string())
        } else {
            Ok(Permission(p))
        }
    }
}
