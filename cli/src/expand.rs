use crate::driver;
use frontend::diagnostics::DiagnosticCollector;
use frontend::macro_expander::{Expander, ExpansionError, MacroTraceEntry};
use frontend::parser::{ParseError, Parser};
use frontend::surface::Syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpandMode {
    SingleStep,
    Full,
    Trace,
}

#[derive(Debug)]
pub enum ExpandError {
    Parse(ParseError),
    Expansion(ExpansionError),
    Import(String),
}

impl std::fmt::Display for ExpandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExpandError::Parse(err) => write!(f, "Parse Error: {:?}", err),
            ExpandError::Expansion(err) => write!(f, "Expansion Error: {:?}", err),
            ExpandError::Import(err) => write!(f, "Import Error: {}", err),
        }
    }
}

pub fn expand_source_with_imports(
    input: &str,
    filename: &str,
    expander: &mut Expander,
    mode: ExpandMode,
) -> Result<String, ExpandError> {
    let mut parser = Parser::new(input);
    let exprs = parser.parse().map_err(ExpandError::Parse)?;
    let module_id = driver::module_id_for_source(filename);
    let mut diagnostics = DiagnosticCollector::new();
    let filtered = driver::apply_macro_imports(expander, &module_id, exprs, &mut diagnostics)
        .map_err(|err| ExpandError::Import(format!("{:?}", err)))?;
    if diagnostics.has_errors() {
        let summary = diagnostics
            .diagnostics
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
            .join("; ");
        return Err(ExpandError::Import(summary));
    }
    let output = format_expansions(filtered, expander, mode)?;
    expander.mark_module_loaded(&module_id);
    Ok(output)
}

pub fn expand_and_format(
    input: &str,
    expander: &mut Expander,
    mode: ExpandMode,
) -> Result<String, ExpandError> {
    let mut parser = Parser::new(input);
    let exprs = parser.parse().map_err(ExpandError::Parse)?;
    format_expansions(exprs, expander, mode)
}

pub fn load_macros_from_source(expander: &mut Expander, source: &str) -> Result<(), ExpandError> {
    let mut parser = Parser::new(source);
    let exprs = parser.parse().map_err(ExpandError::Parse)?;
    for expr in exprs {
        expander
            .expand_all_macros(expr)
            .map_err(ExpandError::Expansion)?;
    }
    Ok(())
}

fn format_expansions(
    exprs: Vec<Syntax>,
    expander: &mut Expander,
    mode: ExpandMode,
) -> Result<String, ExpandError> {
    let mut output = String::new();

    for (idx, expr) in exprs.into_iter().enumerate() {
        if idx > 0 {
            match mode {
                ExpandMode::Trace => output.push_str("\n\n"),
                _ => output.push('\n'),
            }
        }

        match mode {
            ExpandMode::SingleStep => {
                let expanded = expander
                    .expand_syntax_once(expr)
                    .map_err(ExpandError::Expansion)?;
                output.push_str(&expanded.pretty_print_stable());
            }
            ExpandMode::Full => {
                let expanded = expander
                    .expand_syntax(expr)
                    .map_err(ExpandError::Expansion)?;
                output.push_str(&expanded.pretty_print_stable());
            }
            ExpandMode::Trace => {
                let (expanded, trace) = expander
                    .expand_syntax_with_trace(expr)
                    .map_err(ExpandError::Expansion)?;
                output.push_str(&expanded.pretty_print_stable());
                output.push('\n');
                format_trace(&mut output, &trace);
            }
        }
    }

    let _ = expander.take_pending_diagnostics();
    Ok(output)
}

fn format_trace(output: &mut String, trace: &[MacroTraceEntry]) {
    output.push_str("Macro Trace:");
    if trace.is_empty() {
        output.push_str("\n  (none)");
        return;
    }

    for entry in trace {
        let indent = "  ".repeat(entry.depth);
        output.push('\n');
        output.push_str(&format!(
            "{}- {} @ {}:{} [{}..{}]",
            indent, entry.name, entry.span.line, entry.span.col, entry.span.start, entry.span.end
        ));
    }
}
