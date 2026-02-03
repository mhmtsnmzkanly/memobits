//! Memobits interpreter: dosya veya REPL.
//!
//! Kullanım:
//!   cargo run -- <dosya.mb>
//!   cargo run --              # REPL (tek satır)

use std::env;
use std::fs;
use std::io::{self, BufRead, Write};

use memobits::{Interpreter, NativeRegistry, SyntaxAnalyzer};

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
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut interp = Interpreter::new(NativeRegistry::new());

    loop {
        print!("> ");
        let _ = stdout.flush();
        let mut line = String::new();
        if stdin.lock().read_line(&mut line).is_err() || line.is_empty() {
            break;
        }
        let line = line.trim_end();

        if line.is_empty() {
            continue;
        } else if line.starts_with(";q") {
            println!("Quitting repl mode");
            break;
        }
        run_with_interp(&mut interp, line);
    }
}

fn run_with_interp(interp: &mut Interpreter, src: &str) {
    // NOTE: Ana yol artik SyntaxAnalyzer -> AST -> Interpreter.
    let mut sa = SyntaxAnalyzer::new(src);
    match sa.analyz() {
        Ok(program) => {
            if let Err(e) = interp.run(&program) {
                eprintln!("runtime hatası: {}", e);
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
