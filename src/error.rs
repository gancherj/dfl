use lalrpop_util::ParseError;
use std::fmt;
use std::io;

use crate::span::FilePath;
use crate::span::Source;
use crate::span::Span;

#[derive(Debug)]
pub enum Error {
    IOError(io::Error),
    SpannedError(SpannedError),
    OtherError(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::IOError(e) => write!(f, "{}", e),
            Error::SpannedError(e) => write!(f, "{}", e),
            Error::OtherError(e) => write!(f, "{}", e),
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::IOError(err)
    }
}

impl From<SpannedError> for Error {
    fn from(err: SpannedError) -> Self {
        Error::SpannedError(err)
    }
}

impl From<String> for Error {
    fn from(err: String) -> Self {
        Error::OtherError(err)
    }
}

#[derive(Debug)]
pub struct SpannedError {
    pub span: Option<Span>,
    pub msg: String,
}

impl SpannedError {
    pub fn new(msg: impl Into<String>) -> SpannedError {
        SpannedError {
            span: None,
            msg: msg.into(),
        }
    }

    pub fn spanned(span: &Option<Span>, msg: impl Into<String>) -> SpannedError {
        SpannedError {
            span: span.as_ref().cloned(),
            msg: msg.into(),
        }
    }

    pub fn new_err<T>(msg: impl Into<String>) -> Result<T, SpannedError> {
        Err(SpannedError::new(msg))
    }

    pub fn spanned_err<T>(span: &Option<Span>, msg: impl Into<String>) -> Result<T, SpannedError> {
        Err(SpannedError::spanned(span, msg))
    }

    pub fn from_parse_error<T: fmt::Display, E: fmt::Display>(
        path: &FilePath,
        src: &Source,
        err: ParseError<usize, T, E>,
    ) -> SpannedError {
        let (loc, msg) = match err {
            ParseError::InvalidToken { location } => {
                (location, "parse error: invalid token".into())
            }
            ParseError::UnrecognizedEof { location, .. } => {
                (location, "parse error: unexpected eof".into())
            }
            ParseError::UnrecognizedToken {
                token: (start, token, _),
                ..
            } => (start, format!("parse error: unexpected token {}", token)),
            ParseError::ExtraToken {
                token: (start, token, _),
            } => (start, format!("parse error: extra token {}", token)),
            ParseError::User { error } => (0, format!("parse error: {}", error)),
        };
        SpannedError::spanned(
            &Some(Span {
                path: path.clone(),
                source: src.clone(),
                start: loc,
                end: loc,
            }),
            msg,
        )
    }
}

impl fmt::Display for SpannedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}: {}",
            match &self.span {
                Some(span) =>
                    if let Some((line, col)) = span.get_start_line_col_num() {
                        format!("{}:{}:{}", span.path, line, col)
                    } else {
                        "<unknown>".into()
                    },
                None => "<unknown>".into(),
            },
            self.msg
        )
    }
}
