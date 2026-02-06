use crate::surface::Span;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
    Info,
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Level::Error => write!(f, "Error"),
            Level::Warning => write!(f, "Warning"),
            Level::Info => write!(f, "Info"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: Level,
    pub code: Option<&'static str>,
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<(Span, String)>,
}

impl Diagnostic {
    pub fn new(level: Level, message: String) -> Self {
        Self {
            level,
            code: None,
            message,
            span: None,
            labels: Vec::new(),
        }
    }

    pub fn error(message: String) -> Self {
        Self::new(Level::Error, message)
    }

    pub fn warning(message: String) -> Self {
        Self::new(Level::Warning, message)
    }

    pub fn with_code(mut self, code: &'static str) -> Self {
        self.code = Some(code);
        self
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn with_label(mut self, span: Span, message: String) -> Self {
        self.labels.push((span, message));
        self
    }

    pub fn message_with_code(&self) -> String {
        match self.code {
            Some(code) => format!("[{}] {}", code, self.message),
            None => self.message.clone(),
        }
    }
}

pub trait DiagnosticHandler {
    fn handle(&mut self, diagnostic: Diagnostic);
}

// Simple vector collector
pub struct DiagnosticCollector {
    pub diagnostics: Vec<Diagnostic>,
}

impl DiagnosticCollector {
    pub fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
        }
    }

    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.level == Level::Error)
    }
}

impl DiagnosticHandler for DiagnosticCollector {
    fn handle(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }
}
