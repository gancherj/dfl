use core::fmt;
use std::{
    ops::{Deref, DerefMut},
    rc::Rc,
};

use crate::rc_str_type;

rc_str_type!(FilePath, "{}");
rc_str_type!(Source, "{}");

#[derive(Debug, Clone)]
pub struct Span {
    pub path: FilePath,
    pub source: Source,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn get_start_line_col_num(&self) -> Option<(usize, usize)> {
        Self::get_line_col_num(self.source.as_str(), self.start)
    }

    /// Convert source location to line and column numbers
    fn get_line_col_num(src: &str, offset: usize) -> Option<(usize, usize)> {
        if offset > src.len() {
            return None;
        }
    
        let mut line = 1;
        let mut col = 1;
    
        for (idx, ch) in src.char_indices() {
            if idx == offset {
                return Some((line, col));
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
    
        if offset == src.len() {
            Some((line, col))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct Spanned<X> {
    pub span: Option<Span>,
    pub x: X,
}

pub type RcSpanned<X> = Rc<Spanned<X>>;

impl<X> Spanned<X> {
    pub fn new(x: X) -> RcSpanned<X> {
        Rc::new(Spanned { span: None, x })
    }

    pub fn spanned(path: FilePath, source: Source, start: usize, end: usize, x: X) -> RcSpanned<X> {
        Rc::new(Spanned {
            span: Some(Span { path, source, start, end }),
            x,
        })
    }

    pub fn spanned_option(span: &Option<Span>, x: X) -> RcSpanned<X> {
        Rc::new(Spanned { span: span.as_ref().cloned(), x })
    }
}

impl<X> Deref for Spanned<X> {
    type Target = X;

    fn deref(&self) -> &Self::Target {
        &self.x
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.x
    }
}

impl<X> AsRef<X> for Spanned<X> {
    fn as_ref(&self) -> &X {
        &self.x
    }
}

impl<X> fmt::Display for Spanned<X>
where
    X: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.x)
    }
}
