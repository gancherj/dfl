use core::fmt;
use std::{
    ops::{Deref, DerefMut},
    rc::Rc,
};

#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
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

    pub fn spanned(start: usize, end: usize, x: X) -> RcSpanned<X> {
        Rc::new(Spanned {
            span: Some(Span { start, end }),
            x,
        })
    }

    pub fn spanned_option(span: Option<Span>, x: X) -> RcSpanned<X> {
        Rc::new(Spanned { span, x })
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

#[derive(Debug)]
pub struct Error {
    pub span: Option<Span>,
    pub msg: String,
}

impl Error {
    pub fn new(msg: impl Into<String>) -> Error {
        Error {
            span: None,
            msg: msg.into(),
        }
    }

    pub fn spanned(span: Option<Span>, msg: impl Into<String>) -> Error {
        Error {
            span: span,
            msg: msg.into(),
        }
    }

    pub fn new_err<T>(msg: impl Into<String>) -> Result<T, Error> {
        Err(Error::new(msg))
    }

    pub fn spanned_err<T>(span: Option<Span>, msg: impl Into<String>) -> Result<T, Error> {
        Err(Error::spanned(span, msg))
    }
}
