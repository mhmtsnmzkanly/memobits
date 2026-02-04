//! Memobits interpreter: dosya veya REPL.
//!
//! Kullanım:
//!   cargo run -- <dosya.mb>
//!   cargo run --              # REPL (tek satır)

use std::env;
use std::fs;
use std::time::{Duration, Instant};
use sysinfo::{System, Pid};
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
use rustyline::Editor;

use std::path::Path;

use memobits::{Interpreter, NativeRegistry, TypeChecker, load_with_modules};
use memobits::optimizer::optimize_program;

fn main() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let performance = extract_flag(&mut args, "--performance");
    if let Some(path) = args.get(0).cloned() {
        let src = fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("okunamadı {}: {}", path, e);
            std::process::exit(1);
        });

        let native = NativeRegistry::new();
        let mut interp = Interpreter::new(native);
        run_with_interp(&mut interp, &src, Some(Path::new(&path)), performance);
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
        run_with_interp(&mut interp, &buffer, None, false);
        buffer.clear();
    }

    if let Some(ref path) = history_path {
        let _ = rl.save_history(path);
    }
}

fn run_with_interp(interp: &mut Interpreter, src: &str, entry_path: Option<&Path>, performance: bool) {
    let perf_start = Instant::now();
    let mem_start = rss_kb();

    // NOTE: Modül desteği için kaynaklar genişletilir.
    let t0 = Instant::now();
    let mut loaded = match load_with_modules(src, entry_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("modül hatası: {}", e);
            return;
        }
    };
    let load_dur = t0.elapsed();
    let mem_after_load = rss_kb();

    let t1 = Instant::now();
    optimize_program(&mut loaded.program);
    let opt_dur = t1.elapsed();
    let mem_after_opt = rss_kb();

    interp.set_source(&loaded.source);
    let mut tc = TypeChecker::new();
    tc.set_source(&loaded.source);
    let t2 = Instant::now();
    match tc.check_program(&loaded.program) {
        Ok(()) => {
            let type_dur = t2.elapsed();
            let mem_after_type = rss_kb();
            if !tc.warnings().is_empty() {
                eprintln!("type warning:");
                for w in tc.warnings() {
                    eprintln!("  {}", w);
                }
            }
            let t3 = Instant::now();
            let run_res = interp.run(&loaded.program);
            let run_dur = t3.elapsed();
            let mem_after_run = rss_kb();
            if let Err(e) = run_res {
                eprintln!("runtime hatası: {}", e);
            }
            if performance {
                print_perf(
                    perf_start.elapsed(),
                    load_dur,
                    opt_dur,
                    type_dur,
                    run_dur,
                    mem_start,
                    mem_after_load,
                    mem_after_opt,
                    mem_after_type,
                    mem_after_run,
                );
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

fn repl_history_path() -> Option<String> {
    let home = env::var("HOME").ok()?;
    Some(format!("{}/.memobits_history", home))
}

fn extract_flag(args: &mut Vec<String>, flag: &str) -> bool {
    if let Some(pos) = args.iter().position(|a| a == flag) {
        args.remove(pos);
        true
    } else {
        false
    }
}

fn rss_kb() -> Option<u64> {
    let pid = Pid::from_u32(std::process::id());
    let mut sys = System::new_all();
    sys.refresh_process(pid);
    sys.process(pid).map(|p| {
        let mut mem = p.memory();
        // sysinfo's memory unit can vary by platform/build; normalize to KB if it looks like bytes.
        if mem > 1_048_576 && mem % 1024 == 0 {
            mem /= 1024;
        }
        mem
    })
}

fn print_perf(
    total: Duration,
    load: Duration,
    opt: Duration,
    typecheck: Duration,
    runtime: Duration,
    mem_start: Option<u64>,
    mem_after_load: Option<u64>,
    mem_after_opt: Option<u64>,
    mem_after_type: Option<u64>,
    mem_after_run: Option<u64>,
) {
    eprintln!("[performance]");
    eprintln!("  total:     {}", fmt_duration(total));
    eprintln!("  load:      {}", fmt_duration(load));
    eprintln!("  optimize:  {}", fmt_duration(opt));
    eprintln!("  typecheck: {}", fmt_duration(typecheck));
    eprintln!("  runtime:   {}", fmt_duration(runtime));
    if let (Some(a), Some(b), Some(c), Some(d), Some(e)) = (
        mem_start,
        mem_after_load,
        mem_after_opt,
        mem_after_type,
        mem_after_run,
    ) {
        eprintln!("  mem:");
        eprintln!("    start:   {}", fmt_mem(a));
        eprintln!("    load:    {}", fmt_mem(b));
        eprintln!("    optimize:{}", fmt_mem(c));
        eprintln!("    type:    {}", fmt_mem(d));
        eprintln!("    runtime: {}", fmt_mem(e));
    } else {
        eprintln!("  mem: unavailable");
    }
}

fn fmt_duration(d: Duration) -> String {
    let micros = d.as_micros();
    if micros < 1000 {
        format!("{}µs", micros)
    } else if micros < 1_000_000 {
        format!("{:.2}ms", micros as f64 / 1000.0)
    } else {
        format!("{:.2}s", micros as f64 / 1_000_000.0)
    }
}

fn fmt_mem(kb: u64) -> String {
    if kb < 1024 {
        return format!("{} KB", kb);
    }
    let mb = kb as f64 / 1024.0;
    format!("{:.2} MB", mb)
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
