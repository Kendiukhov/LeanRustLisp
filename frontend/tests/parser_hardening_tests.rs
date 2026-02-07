use frontend::declaration_parser::DeclarationParser;
use frontend::macro_expander::Expander;
use frontend::parser::{ParseError, Parser};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::{Mutex, OnceLock};

fn parser_hardening_test_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn is_libtest_noise_line(line: &str) -> bool {
    let trimmed = line.trim();
    (trimmed.starts_with("running ") && trimmed.ends_with(" tests"))
        || trimmed.starts_with("test result:")
        || trimmed.starts_with("test ")
            && (trimmed.ends_with(" ... ok")
                || trimmed.ends_with(" ... FAILED")
                || trimmed.ends_with(" ... ignored"))
}

#[cfg(unix)]
fn capture_stdout<F: FnOnce()>(f: F) -> String {
    use std::io::Write;
    use std::os::raw::c_int;

    extern "C" {
        fn close(fd: c_int) -> c_int;
        fn dup(fd: c_int) -> c_int;
        fn dup2(oldfd: c_int, newfd: c_int) -> c_int;
        fn pipe(fds: *mut c_int) -> c_int;
        fn read(fd: c_int, buf: *mut core::ffi::c_void, count: usize) -> isize;
    }

    const STDOUT_FILENO: c_int = 1;

    let mut pipe_fds = [0; 2];
    // SAFETY: libc calls are checked for failure and used only with valid file descriptors.
    unsafe {
        assert_eq!(pipe(pipe_fds.as_mut_ptr()), 0, "pipe() failed");
        let read_fd = pipe_fds[0];
        let write_fd = pipe_fds[1];

        let saved_stdout = dup(STDOUT_FILENO);
        assert!(saved_stdout >= 0, "dup() failed");
        assert_eq!(
            dup2(write_fd, STDOUT_FILENO),
            STDOUT_FILENO,
            "dup2() failed"
        );
        assert_eq!(close(write_fd), 0, "close(write_fd) failed");

        let run_result = catch_unwind(AssertUnwindSafe(f));
        let _ = std::io::stdout().flush();

        assert_eq!(
            dup2(saved_stdout, STDOUT_FILENO),
            STDOUT_FILENO,
            "restore dup2() failed"
        );
        assert_eq!(close(saved_stdout), 0, "close(saved_stdout) failed");

        let mut output = Vec::new();
        let mut buf = [0u8; 1024];
        loop {
            let bytes_read = read(read_fd, buf.as_mut_ptr().cast(), buf.len());
            if bytes_read <= 0 {
                break;
            }
            output.extend_from_slice(&buf[..bytes_read as usize]);
        }
        assert_eq!(close(read_fd), 0, "close(read_fd) failed");

        if let Err(panic_payload) = run_result {
            resume_unwind(panic_payload);
        }

        String::from_utf8_lossy(&output).into_owned()
    }
}

#[cfg(not(unix))]
fn capture_stdout<F: FnOnce()>(f: F) -> String {
    f();
    String::new()
}

#[test]
fn oversized_integer_literal_reports_overflow_without_panic() {
    let _guard = parser_hardening_test_lock()
        .lock()
        .expect("parser hardening lock poisoned");
    let input = format!("({})", "9".repeat(512));
    let mut parser = Parser::new(&input);
    let err = parser
        .parse()
        .expect_err("oversized integer literal should not parse as usize");

    assert_eq!(err.diagnostic_code(), "F0005");
    match err {
        ParseError::IntegerOverflow(literal, span) => {
            assert_eq!(literal.len(), 512);
            assert!(span.end > span.start);
            assert_eq!(span.line, 1);
        }
        other => panic!("expected IntegerOverflow parse error, got {:?}", other),
    }
}

#[test]
fn declaration_parse_failure_does_not_emit_stdout_debug_noise() {
    let _guard = parser_hardening_test_lock()
        .lock()
        .expect("parser hardening lock poisoned");
    let mut parser = Parser::new("(defmacro broken)");
    let syntax_nodes = parser
        .parse()
        .expect("parser should accept defmacro syntax");

    let output = capture_stdout(|| {
        let mut expander = Expander::new();
        let mut declaration_parser = DeclarationParser::new(&mut expander);
        let result = declaration_parser.parse(syntax_nodes.clone());
        assert!(result.is_err(), "declaration parse should fail");
    });

    let unexpected_lines: Vec<&str> = output
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !is_libtest_noise_line(line))
        .collect();
    assert!(
        unexpected_lines.is_empty(),
        "unexpected stdout from declaration parser: {:?}",
        output
    );
}
