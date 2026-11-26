//! Shortest round-trip decimal text for `f32` and `f64`, in the guest.
//!
//! This is the Burger-Dybvig free-format algorithm (the same digits as Rust's
//! `Display`, which is what string interpolation promises) on fixed-size
//! big integers kept in a static scratch region: no tables, no heap, and the
//! module only carries these functions when a float placeholder is reachable.
//!
//! Layout of the scratch region (`SCRATCH_BYTES`): five 40-limb big integers
//! `r`, `s`, `m+`, `m-`, `t` (little-endian `u32` limbs, 1280 bits, enough for
//! every `f64` including the `x10` headroom), 32 digit bytes, then the text
//! buffer (the longest text, the smallest subnormal, is 327 bytes).
//!
//! The functions are written in a tiny line-free text assembler (`assemble`)
//! so the control flow stays reviewable. Operands: `$name` locals/labels,
//! numbers, `call $function`. Pseudo instructions: `addr $base $index`
//! (address of a `u32` limb), `putc` (store the byte on the stack at `$pos`),
//! `adv` (add the count on the stack to `$pos`).

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

pub(super) const FUNCTION_COUNT: u32 = 8;
const LIMBS: u32 = 40;
const BIG_BYTES: u32 = LIMBS * 4;
const DIGIT_OFFSET: u32 = 5 * BIG_BYTES;
const TEXT_OFFSET: u32 = DIGIT_OFFSET + 32;
const TEXT_BYTES: u32 = 336;
pub(super) const SCRATCH_BYTES: u32 = TEXT_OFFSET + TEXT_BYTES;

/// The function types, in the order of the functions.
pub(super) fn signatures() -> Vec<(Vec<ValType>, Vec<ValType>)> {
    use ValType::{I32, I64};
    vec![
        (vec![I32, I64, I32], vec![]),    // big_set
        (vec![I32, I32], vec![]),         // big_mul
        (vec![I32, I32], vec![I32]),      // big_cmp
        (vec![I32, I32], vec![]),         // big_sub
        (vec![I32, I32, I32], vec![]),    // big_add
        (vec![I32, I32], vec![]),         // big_pow10
        (vec![I64, I32], vec![I32]),      // float_text
        (vec![I32, I64, I32], vec![I32]), // float_write
    ]
}

/// The functions, in order. `first` is the module index of `big_set`;
/// `scratch` the address of the scratch region.
pub(super) fn functions(first: u32, scratch: u32) -> Vec<WasmFunction> {
    let callees = [
        ("big_set", first),
        ("big_mul", first + 1),
        ("big_cmp", first + 2),
        ("big_sub", first + 3),
        ("big_add", first + 4),
        ("big_pow10", first + 5),
        ("float_text", first + 6),
    ];
    use ValType::{I32, I64};
    let r = scratch;
    let s = scratch + BIG_BYTES;
    let mp = scratch + 2 * BIG_BYTES;
    let mm = scratch + 3 * BIG_BYTES;
    let t = scratch + 4 * BIG_BYTES;
    let digits = scratch + DIGIT_OFFSET;
    let text = scratch + TEXT_OFFSET;
    let top = LIMBS - 1;
    let word = |bytes: &[u8; 4]| i32::from_le_bytes(*bytes);
    vec![
        assemble(
            &[("a", I32), ("v", I64), ("shift", I32)],
            &[("i", I32), ("limbs", I32), ("b", I32), ("j", I32), ("hi", I32), ("lo", I32)],
            &callees,
            &format!(
                "
                i32.const 0 local.set $i
                loop $clear
                  addr $a $i i32.const 0 i32.store 0
                  local.get $i i32.const 1 i32.add local.tee $i i32.const {LIMBS} i32.lt_u br_if $clear
                end
                local.get $a local.get $v i32.wrap_i64 i32.store 0
                local.get $a local.get $v i64.const 32 i64.shr_u i32.wrap_i64 i32.store 4
                local.get $shift i32.eqz if $none return end
                local.get $shift i32.const 5 i32.shr_u local.set $limbs
                local.get $shift i32.const 31 i32.and local.set $b
                i32.const {top} local.set $i
                loop $shl
                  i32.const 0 local.set $hi
                  i32.const 0 local.set $lo
                  local.get $i local.get $limbs i32.ge_s
                  if $inside
                    local.get $i local.get $limbs i32.sub local.set $j
                    addr $a $j i32.load 0 local.set $hi
                    local.get $j i32.const 1 i32.ge_s
                    if $below
                      local.get $j i32.const 1 i32.sub local.set $j
                      addr $a $j i32.load 0 local.set $lo
                    end
                  end
                  addr $a $i
                  local.get $hi local.get $b i32.shl
                  local.get $lo i32.const 1 i32.shr_u i32.const 31 local.get $b i32.sub i32.shr_u
                  i32.or i32.store 0
                  local.get $i i32.const 1 i32.sub local.tee $i i32.const 0 i32.ge_s br_if $shl
                end
                "
            ),
        ),
        assemble(
            &[("a", I32), ("m", I32)],
            &[("i", I32), ("c", I64), ("p", I64)],
            &callees,
            &format!(
                "
                i32.const 0 local.set $i
                loop $l
                  addr $a $i i32.load 0 i64.extend_i32_u local.get $m i64.extend_i32_u i64.mul
                  local.get $c i64.add local.set $p
                  addr $a $i local.get $p i32.wrap_i64 i32.store 0
                  local.get $p i64.const 32 i64.shr_u local.set $c
                  local.get $i i32.const 1 i32.add local.tee $i i32.const {LIMBS} i32.lt_u br_if $l
                end
                "
            ),
        ),
        assemble(
            &[("a", I32), ("b", I32)],
            &[("i", I32), ("x", I32), ("y", I32)],
            &callees,
            &format!(
                "
                i32.const {top} local.set $i
                loop $l
                  addr $a $i i32.load 0 local.set $x
                  addr $b $i i32.load 0 local.set $y
                  local.get $x local.get $y i32.ne
                  if $differ
                    i32.const -1 i32.const 1 local.get $x local.get $y i32.lt_u select return
                  end
                  local.get $i i32.const 1 i32.sub local.tee $i i32.const 0 i32.ge_s br_if $l
                end
                i32.const 0
                "
            ),
        ),
        assemble(
            &[("a", I32), ("b", I32)],
            &[("i", I32), ("t", I64), ("borrow", I64)],
            &callees,
            &format!(
                "
                i32.const 0 local.set $i
                loop $l
                  addr $a $i i32.load 0 i64.extend_i32_u
                  addr $b $i i32.load 0 i64.extend_i32_u i64.sub
                  local.get $borrow i64.sub local.set $t
                  addr $a $i local.get $t i32.wrap_i64 i32.store 0
                  local.get $t i64.const 63 i64.shr_u local.set $borrow
                  local.get $i i32.const 1 i32.add local.tee $i i32.const {LIMBS} i32.lt_u br_if $l
                end
                "
            ),
        ),
        assemble(
            &[("d", I32), ("a", I32), ("b", I32)],
            &[("i", I32), ("t", I64), ("carry", I64)],
            &callees,
            &format!(
                "
                i32.const 0 local.set $i
                loop $l
                  addr $a $i i32.load 0 i64.extend_i32_u
                  addr $b $i i32.load 0 i64.extend_i32_u i64.add
                  local.get $carry i64.add local.set $t
                  addr $d $i local.get $t i32.wrap_i64 i32.store 0
                  local.get $t i64.const 32 i64.shr_u local.set $carry
                  local.get $i i32.const 1 i32.add local.tee $i i32.const {LIMBS} i32.lt_u br_if $l
                end
                "
            ),
        ),
        assemble(
            &[("a", I32), ("n", I32)],
            &[("p", I32)],
            &callees,
            "
            block $done
              loop $l
                local.get $n i32.const 9 i32.lt_s br_if $done
                local.get $a i32.const 1000000000 call $big_mul
                local.get $n i32.const 9 i32.sub local.set $n
                br $l
              end
            end
            i32.const 1 local.set $p
            block $done2
              loop $m
                local.get $n i32.eqz br_if $done2
                local.get $p i32.const 10 i32.mul local.set $p
                local.get $n i32.const 1 i32.sub local.set $n
                br $m
              end
            end
            local.get $a local.get $p call $big_mul
            ",
        ),
        assemble(
            &[("bits", I64), ("is32", I32)],
            &[
                ("neg", I32), ("ex", I32), ("fr", I64), ("mbits", I32), ("bias", I32),
                ("maxex", I32), ("f", I64), ("e", I32), ("asym", I32), ("incl", I32),
                ("nonneg", I32), ("k", I32), ("n", I32), ("d", I32), ("c", I32), ("low", I32),
                ("high", I32), ("pos", I32), ("ch", I32), ("i", I32),
            ],
            &callees,
            &format!(
                "
                local.get $is32
                if $decode
                  local.get $bits i64.const 31 i64.shr_u i32.wrap_i64 i32.const 1 i32.and local.set $neg
                  local.get $bits i64.const 23 i64.shr_u i32.wrap_i64 i32.const 255 i32.and local.set $ex
                  local.get $bits i64.const 8388607 i64.and local.set $fr
                  i32.const 23 local.set $mbits i32.const 150 local.set $bias i32.const 255 local.set $maxex
                else
                  local.get $bits i64.const 63 i64.shr_u i32.wrap_i64 local.set $neg
                  local.get $bits i64.const 52 i64.shr_u i32.wrap_i64 i32.const 2047 i32.and local.set $ex
                  local.get $bits i64.const 4503599627370495 i64.and local.set $fr
                  i32.const 52 local.set $mbits i32.const 1075 local.set $bias i32.const 2047 local.set $maxex
                end
                i32.const {text} local.set $pos
                local.get $ex local.get $maxex i32.eq local.get $fr i64.eqz i32.eqz i32.and
                if $nan
                  i32.const {text} i32.const {nan} i32.store 0
                  i32.const 3 return
                end
                local.get $neg if $sign i32.const 45 putc end
                local.get $ex local.get $maxex i32.eq
                if $inf
                  local.get $pos i32.const {inf} i32.store 0
                  i32.const 3 adv {finish} return
                end
                local.get $ex i32.eqz local.get $fr i64.eqz i32.and
                if $zero i32.const 48 putc {finish} return end
                local.get $ex i32.eqz
                if $subnormal
                  local.get $fr local.set $f
                  i32.const 1 local.get $bias i32.sub local.set $e
                else
                  local.get $fr i64.const 1 local.get $mbits i64.extend_i32_u i64.shl i64.or local.set $f
                  local.get $ex local.get $bias i32.sub local.set $e
                end
                local.get $fr i64.eqz local.get $ex i32.const 1 i32.gt_u i32.and local.set $asym
                local.get $f i64.const 1 i64.and i64.eqz local.set $incl
                local.get $e i32.const 0 i32.ge_s local.set $nonneg
                i32.const {r} local.get $f
                  local.get $e i32.const 0 local.get $nonneg select i32.const 1 i32.add local.get $asym i32.add
                  call $big_set
                i32.const {s}
                  i64.const 2 local.get $asym i64.extend_i32_u i64.shl i64.const 1 local.get $nonneg select
                  i32.const 0 i32.const 1 local.get $asym i32.add local.get $e i32.sub local.get $nonneg select
                  call $big_set
                i32.const {mp}
                  i64.const 1 i64.const 1 local.get $asym i64.extend_i32_u i64.shl local.get $nonneg select
                  local.get $e local.get $asym i32.add i32.const 0 local.get $nonneg select
                  call $big_set
                i32.const {mm} i64.const 1 local.get $e i32.const 0 local.get $nonneg select call $big_set
                ;; k = ceil(log10(2) * floor(log2 v) - 1e-10): never above the true value, at most one below
                local.get $e i32.const 63 i32.add local.get $f i64.clz i32.wrap_i64 i32.sub
                f64.convert_i32_s f64.const 0.30102999566398114 f64.mul f64.const 1e-10 f64.sub
                f64.ceil i32.trunc_f64_s local.set $k
                local.get $k i32.const 0 i32.ge_s
                if $up
                  i32.const {s} local.get $k call $big_pow10
                else
                  i32.const {r} i32.const 0 local.get $k i32.sub call $big_pow10
                  i32.const {mp} i32.const 0 local.get $k i32.sub call $big_pow10
                  i32.const {mm} i32.const 0 local.get $k i32.sub call $big_pow10
                end
                i32.const {t} i32.const {r} i32.const {mp} call $big_add
                i32.const {t} i32.const {s} call $big_cmp i32.const 0 local.get $incl i32.sub i32.gt_s
                if $fix
                  i32.const {s} i32.const 10 call $big_mul
                  local.get $k i32.const 1 i32.add local.set $k
                end
                loop $digit
                  i32.const {r} i32.const 10 call $big_mul
                  i32.const {mp} i32.const 10 call $big_mul
                  i32.const {mm} i32.const 10 call $big_mul
                  i32.const 0 local.set $d
                  block $out
                    loop $count
                      i32.const {r} i32.const {s} call $big_cmp i32.const 0 i32.lt_s br_if $out
                      i32.const {r} i32.const {s} call $big_sub
                      local.get $d i32.const 1 i32.add local.set $d
                      br $count
                    end
                  end
                  i32.const {r} i32.const {mm} call $big_cmp local.get $incl i32.lt_s local.set $low
                  i32.const {t} i32.const {r} i32.const {mp} call $big_add
                  i32.const {t} i32.const {s} call $big_cmp i32.const 0 local.get $incl i32.sub i32.gt_s local.set $high
                  local.get $low local.get $high i32.or i32.eqz
                  if $more
                    i32.const {digits} local.get $n i32.add local.get $d i32.const 48 i32.add i32.store8 0
                    local.get $n i32.const 1 i32.add local.set $n
                    br $digit
                  end
                  local.get $high
                  if $round
                    local.get $low
                    if $tie
                      i32.const {t} i32.const {r} i32.const {r} call $big_add
                      i32.const {t} i32.const {s} call $big_cmp i32.const 0 i32.ge_s local.set $c
                    else
                      i32.const 1 local.set $c
                    end
                    local.get $d local.get $c i32.add local.set $d
                  end
                  i32.const {digits} local.get $n i32.add local.get $d i32.const 48 i32.add i32.store8 0
                  local.get $n i32.const 1 i32.add local.set $n
                end
                local.get $k i32.const 0 i32.le_s
                if $small
                  i32.const 48 putc i32.const 46 putc
                  local.get $pos i32.const 48 i32.const 0 local.get $k i32.sub memory.fill
                  i32.const 0 local.get $k i32.sub adv
                  local.get $pos i32.const {digits} local.get $n memory.copy
                  local.get $n adv
                else
                  local.get $k local.get $n i32.ge_s
                  if $integral
                    local.get $pos i32.const {digits} local.get $n memory.copy
                    local.get $n adv
                    local.get $pos i32.const 48 local.get $k local.get $n i32.sub memory.fill
                    local.get $k local.get $n i32.sub adv
                  else
                    local.get $pos i32.const {digits} local.get $k memory.copy
                    local.get $k adv
                    i32.const 46 putc
                    local.get $pos i32.const {digits} local.get $k i32.add local.get $n local.get $k i32.sub memory.copy
                    local.get $n local.get $k i32.sub adv
                  end
                end
                {finish}
                ",
                finish = format!("local.get $pos i32.const {text} i32.sub"),
                nan = word(b"NaN\0"),
                inf = word(b"inf\0"),
            ),
        ),
        assemble(
            &[("dest", I32), ("bits", I64), ("is32", I32)],
            &[("len", I32)],
            &callees,
            &format!(
                "
                local.get $bits local.get $is32 call $float_text local.set $len
                local.get $dest i32.const {text} local.get $len memory.copy
                local.get $len
                "
            ),
        ),
    ]
}

fn mem(offset: u64) -> MemArg {
    MemArg {
        offset,
        align: 0,
        target: wasm_encoder::MemArgTarget::Memory(0),
        ordering: None,
    }
}

/// Assemble one function body. Panics on malformed source: the sources are
/// compile-time constants covered by the unit tests below.
fn assemble(
    params: &[(&str, ValType)],
    locals: &[(&str, ValType)],
    callees: &[(&str, u32)],
    source: &str,
) -> WasmFunction {
    let names: Vec<&str> = params.iter().chain(locals).map(|(n, _)| *n).collect();
    let mut function = WasmFunction::new(locals.iter().map(|(_, ty)| (1, *ty)));
    let local = |name: &str| names.iter().position(|n| *n == name).unwrap() as u32;
    let mut labels: Vec<&str> = Vec::new();
    // The source has `;;` comments to the end of the line.
    let cleaned: String = source
        .lines()
        .map(|line| line.split(";;").next().unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    let mut tokens = cleaned.split_whitespace();
    macro_rules! next {
        () => {
            tokens.next().expect("missing operand")
        };
    }
    while let Some(token) = tokens.next() {
        let instruction = match token {
            "local.get" => I::LocalGet(local(next!().trim_start_matches('$'))),
            "local.set" => I::LocalSet(local(next!().trim_start_matches('$'))),
            "local.tee" => I::LocalTee(local(next!().trim_start_matches('$'))),
            "i32.const" => I::I32Const(next!().parse().unwrap()),
            "i64.const" => I::I64Const(next!().parse().unwrap()),
            "f64.const" => I::F64Const(next!().parse::<f64>().unwrap().into()),
            "call" => {
                let name = next!().trim_start_matches('$');
                I::Call(callees.iter().find(|(n, _)| *n == name).unwrap().1)
            }
            "block" | "loop" | "if" => {
                labels.push(next!().trim_start_matches('$'));
                match token {
                    "block" => I::Block(BlockType::Empty),
                    "loop" => I::Loop(BlockType::Empty),
                    _ => I::If(BlockType::Empty),
                }
            }
            "else" => I::Else,
            "end" => {
                labels.pop().unwrap();
                I::End
            }
            "br" | "br_if" => {
                let name = next!().trim_start_matches('$');
                let depth = labels.iter().rev().position(|l| *l == name).unwrap() as u32;
                if token == "br" {
                    I::Br(depth)
                } else {
                    I::BrIf(depth)
                }
            }
            "return" => I::Return,
            "select" => I::Select,
            "i32.load" => I::I32Load(mem(next!().parse().unwrap())),
            "i32.store" => I::I32Store(mem(next!().parse().unwrap())),
            "i32.store8" => I::I32Store8(mem(next!().parse().unwrap())),
            "memory.copy" => I::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            },
            "memory.fill" => I::MemoryFill(0),
            "i32.add" => I::I32Add,
            "i32.sub" => I::I32Sub,
            "i32.mul" => I::I32Mul,
            "i32.and" => I::I32And,
            "i32.or" => I::I32Or,
            "i32.shl" => I::I32Shl,
            "i32.shr_u" => I::I32ShrU,
            "i32.eqz" => I::I32Eqz,
            "i32.eq" => I::I32Eq,
            "i32.ne" => I::I32Ne,
            "i32.lt_s" => I::I32LtS,
            "i32.lt_u" => I::I32LtU,
            "i32.gt_s" => I::I32GtS,
            "i32.gt_u" => I::I32GtU,
            "i32.le_s" => I::I32LeS,
            "i32.ge_s" => I::I32GeS,
            "i32.wrap_i64" => I::I32WrapI64,
            "i64.extend_i32_u" => I::I64ExtendI32U,
            "i64.add" => I::I64Add,
            "i64.sub" => I::I64Sub,
            "i64.mul" => I::I64Mul,
            "i64.and" => I::I64And,
            "i64.or" => I::I64Or,
            "i64.shl" => I::I64Shl,
            "i64.shr_u" => I::I64ShrU,
            "i64.eqz" => I::I64Eqz,
            "i64.clz" => I::I64Clz,
            "f64.convert_i32_s" => I::F64ConvertI32S,
            "f64.mul" => I::F64Mul,
            "f64.sub" => I::F64Sub,
            "f64.ceil" => I::F64Ceil,
            "i32.trunc_f64_s" => I::I32TruncF64S,
            "addr" => {
                let base = local(next!().trim_start_matches('$'));
                let index = local(next!().trim_start_matches('$'));
                function.instruction(&I::LocalGet(base));
                function.instruction(&I::LocalGet(index));
                function.instruction(&I::I32Const(2));
                function.instruction(&I::I32Shl);
                I::I32Add
            }
            "putc" => {
                function.instruction(&I::LocalSet(local("ch")));
                function.instruction(&I::LocalGet(local("pos")));
                function.instruction(&I::LocalGet(local("ch")));
                function.instruction(&I::I32Store8(mem(0)));
                function.instruction(&I::I32Const(1));
                function.instruction(&I::LocalGet(local("pos")));
                function.instruction(&I::I32Add);
                I::LocalSet(local("pos"))
            }
            "adv" => {
                function.instruction(&I::LocalGet(local("pos")));
                function.instruction(&I::I32Add);
                I::LocalSet(local("pos"))
            }
            other => panic!("unknown mnemonic {other}"),
        };
        function.instruction(&instruction);
    }
    function.instruction(&I::End);
    function
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_encoder::{
        CodeSection, ExportKind, ExportSection, FunctionSection, MemorySection, MemoryType, Module,
        TypeSection,
    };

    /// A module with the float functions only; `float_write(dest, bits, is32)`.
    fn module() -> Vec<u8> {
        let mut types = TypeSection::new();
        let mut functions = FunctionSection::new();
        let mut code = CodeSection::new();
        for (index, (params, results)) in signatures().into_iter().enumerate() {
            types.ty().function(params, results);
            functions.function(index as u32);
        }
        for function in functions_at(0, 4096) {
            code.function(&function);
        }
        let mut exports = ExportSection::new();
        exports.export("float_write", ExportKind::Func, 7);
        exports.export("memory", ExportKind::Memory, 0);
        let mut memories = MemorySection::new();
        memories.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        let mut module = Module::new();
        module
            .section(&types)
            .section(&functions)
            .section(&memories)
            .section(&exports)
            .section(&code);
        module.finish()
    }

    fn functions_at(first: u32, scratch: u32) -> Vec<WasmFunction> {
        functions(first, scratch)
    }

    #[test]
    fn matches_rust_display_for_boundaries_and_pseudo_random_patterns() {
        run_table();
    }

    fn run_table() {
        use wasmi::{Engine, Linker, Module as WasmiModule, Store};
        let bytes = module();
        wasmparser::Validator::new().validate_all(&bytes).unwrap();
        let engine = Engine::default();
        let module = WasmiModule::new(&engine, &bytes[..]).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Linker::new(&engine)
            .instantiate_and_start(&mut store, &module)
            .unwrap();
        let write = instance
            .get_typed_func::<(i32, i64, i32), i32>(&store, "float_write")
            .unwrap();
        let memory = instance.get_memory(&store, "memory").unwrap();
        let mut check = |bits: u64, is32: bool, expected: String| {
            let len = write
                .call(&mut store, (0, bits as i64, i32::from(is32)))
                .unwrap();
            let mut text = vec![0u8; len as usize];
            memory.read(&store, 0, &mut text).unwrap();
            assert_eq!(
                String::from_utf8(text).unwrap(),
                expected,
                "{bits:#x} {is32}"
            );
        };
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let edge64 = [
            0u64,
            1,
            2,
            0x8000_0000_0000_0000,
            0x7ff0_0000_0000_0000,
            0xfff0_0000_0000_0000,
            0x7ff8_0000_0000_0000,
            0xfff8_0000_0000_0001,
            0x7fef_ffff_ffff_ffff,
            0x0010_0000_0000_0000,
            0x000f_ffff_ffff_ffff,
            0x3ff0_0000_0000_0000,
        ];
        for bits in edge64 {
            check(bits, false, format!("{}", f64::from_bits(bits)));
        }
        for _ in 0..2500 {
            let bits = next();
            check(bits, false, format!("{}", f64::from_bits(bits)));
        }
        for exponent in -323..=308 {
            let value: f64 = format!("1e{exponent}").parse().unwrap();
            for bits in [value.to_bits() - 1, value.to_bits(), value.to_bits() + 1] {
                check(bits, false, format!("{}", f64::from_bits(bits)));
            }
        }
        for _ in 0..2500 {
            let bits = next() as u32;
            check(u64::from(bits), true, format!("{}", f32::from_bits(bits)));
        }
        for exponent in -45..=38 {
            let value: f32 = format!("1e{exponent}").parse().unwrap();
            for bits in [value.to_bits() - 1, value.to_bits(), value.to_bits() + 1] {
                check(u64::from(bits), true, format!("{}", f32::from_bits(bits)));
            }
        }
    }
}
