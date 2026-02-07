use crate::surface::Span;
use std::fmt;

fn is_unknown_span(span: Span) -> bool {
    span.start == 0 && span.end == 0 && span.line == 0 && span.col == 0
}

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
        if !is_unknown_span(span) {
            self.span = Some(span);
        }
        self
    }

    pub fn with_label(mut self, span: Span, message: String) -> Self {
        if !is_unknown_span(span) {
            self.labels.push((span, message));
        }
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

impl Default for DiagnosticCollector {
    fn default() -> Self {
        Self::new()
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn with_span_ignores_unknown_sentinel_span() {
        let diagnostic = Diagnostic::error("test".to_string()).with_span(Span {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        });
        assert!(diagnostic.span.is_none());
    }

    #[test]
    fn with_span_keeps_real_zero_offset_span() {
        let span = Span {
            start: 0,
            end: 0,
            line: 1,
            col: 0,
        };
        let diagnostic = Diagnostic::error("test".to_string()).with_span(span);
        assert_eq!(diagnostic.span, Some(span));
    }
}
