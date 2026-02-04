//! Memobits interpreter: dosya veya REPL.
//!
//! Kullanım:
//!   cargo run -- <dosya.mb>
//!   cargo run --              # REPL (tek satır)

use std::env;
use std::fs;
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::Editor;

use memobits::{Interpreter, NativeRegistry, SyntaxAnalyzer, TypeChecker};

fn main() {
    let mut args = env::args().skip(1);
    if let Some(path) = args.next() {
        let src = fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("okunamadı {}: {}", path, e);
            std::process::exit(1);
        });

        let native = NativeRegistry::new();
        let mut interp = Interpreter::new(native);
        run_with_interp(&mut interp, &src);
        return;
    }

    println!("[ repl mode on ]\nfor quitting repl mode use \";q\" command");
    let mut interp = Interpreter::new(NativeRegistry::new());
    let mut rl = Editor::<(), DefaultHistory>::new().unwrap();
    let history_path = repl_history_path();
    if let Some(ref path) = history_path {
        let _ = rl.load_history(path);
    }

    let mut buffer = String::new();
    loop {
        let prompt = if buffer.is_empty() { "> " } else { "... " };
        let line = match rl.readline(prompt) {
            Ok(line) => line,
            Err(ReadlineError::Interrupted) => {
                if buffer.is_empty() {
                    break;
                }
                buffer.clear();
                continue;
            }
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("repl error: {}", e);
                break;
            }
        };
        let line = line.trim_end();

        if buffer.is_empty() && line.is_empty() {
            continue;
        }
        if buffer.is_empty() && line.starts_with(";q") {
            println!("Quitting repl mode");
            break;
        }
        let _ = rl.add_history_entry(line);
        if !buffer.is_empty() {
            buffer.push('\n');
        }
        buffer.push_str(line);
        if needs_more_input(&buffer) {
            continue;
        }
        run_with_interp(&mut interp, &buffer);
        buffer.clear();
    }

    if let Some(ref path) = history_path {
        let _ = rl.save_history(path);
    }
}

fn run_with_interp(interp: &mut Interpreter, src: &str) {
    // NOTE: Ana yol artik SyntaxAnalyzer -> AST -> Interpreter.
    interp.set_source(src);
    let mut sa = SyntaxAnalyzer::new(src);
    match sa.analyz() {
        Ok(program) => {
            let mut tc = TypeChecker::new();
            tc.set_source(src);
            match tc.check_program(&program) {
                Ok(()) => {
                    if !tc.warnings().is_empty() {
                        eprintln!("type warning:");
                        for w in tc.warnings() {
                            eprintln!("  {}", w);
                        }
                    }
                    if let Err(e) = interp.run(&program) {
                        eprintln!("runtime hatası: {}", e);
                    }
                }
                Err(errs) => {
                    eprintln!("type hatası:");
                    for e in errs {
                        eprintln!("  {}", e);
                    }
                }
            }
        }
        Err(errs) => {
            eprintln!("syntax hatası:");
            for e in errs {
                eprintln!("  {}", e);
            }
        }
    }
}

fn repl_history_path() -> Option<String> {
    let home = env::var("HOME").ok()?;
    Some(format!("{}/.memobits_history", home))
}

fn needs_more_input(src: &str) -> bool {
    let mut paren = 0i32;
    let mut brace = 0i32;
    let mut bracket = 0i32;
    let mut in_str = false;
    let mut in_char = false;
    let mut in_template = false;
    let mut escape = false;

    for ch in src.chars() {
        if in_str {
            if escape {
                escape = false;
                continue;
            }
            if ch == '\\' {
                escape = true;
                continue;
            }
            if ch == '"' {
                in_str = false;
            }
            continue;
        }
        if in_char {
            if escape {
                escape = false;
                continue;
            }
            if ch == '\\' {
                escape = true;
                continue;
            }
            if ch == '\'' {
                in_char = false;
            }
            continue;
        }
        if in_template {
            if escape {
                escape = false;
                continue;
            }
            if ch == '\\' {
                escape = true;
                continue;
            }
            if ch == '`' {
                in_template = false;
            }
            continue;
        }

        match ch {
            '"' => in_str = true,
            '\'' => in_char = true,
            '`' => in_template = true,
            '(' => paren += 1,
            ')' => paren -= 1,
            '{' => brace += 1,
            '}' => brace -= 1,
            '[' => bracket += 1,
            ']' => bracket -= 1,
            _ => {}
        }
    }

    paren > 0 || brace > 0 || bracket > 0
}
