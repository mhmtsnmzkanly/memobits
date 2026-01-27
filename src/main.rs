//! Memobits interpreter: dosya veya REPL.
//!
//! Kullanım:
//!   cargo run -- <dosya.mb>
//!   cargo run --              # REPL (tek satır)

use std::env;
use std::fs;
use std::io::{self, BufRead, Write};

use memobits::{Interpreter, Lexer, NativeRegistry, Parser};

fn main() {
    println!("Memobits interpreter\n");
    let mut args = env::args().skip(1);
    if let Some(path) = args.next() {
        run_file(&path);
        return;
    }

    println!("[ repl mode on ]");
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
        }
        run_with_interp(&mut interp, line);
    }
}

fn run_file(path: &str) {
    let src = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("okunamadı {}: {}", path, e);
        std::process::exit(1);
    });
    run(&src);
}


fn run(src: &str) {
    let native = NativeRegistry::new();
    let mut interp = Interpreter::new(native);
    run_with_interp(&mut interp, src);
}

fn run_with_interp(interp: &mut Interpreter, src: &str) {
    let tokens = match Lexer::new(src).lex() {
        Ok(t) => t,
        Err(e) => {
            eprintln!("lex hatası:");
            for m in e {
                eprintln!("  {}", m);
            }
            return;
        }
    };

    let program = match Parser::new(tokens).parse() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("parse hatası:");
            for m in e {
                eprintln!("  {}: {:?}", m.0, m.1);
            }
            return;
        }
    };

    if let Err(e) = interp.run(&program) {
        eprintln!("runtime hatası: {}", e);
    }
}
