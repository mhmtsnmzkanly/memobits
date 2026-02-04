# Memobits

Rust ve Haskell’den ilham alan, statik tipli, tip çıkarımlı bir programlama dili. AST-walking interpreter Rust ile yazılmıştır.

## Özellikler

- **Bloklar** `{}` ile; indentation semantik değil
- **let** (immutable) / **var** (mutable)
- **struct**, **enum**, **match** (exhaustive)
- **fn**, lambda, **native::** host entegrasyonu
- **if** / **else**, **loop** / **break** / **continue**
- **Option** / **Result** benzeri hata modeli
- Template string: `` `Merhaba {id}` `` (v1’de yalnızca `{id}`)
- `Map` index okuma/atama (`m[key]`, `m[key] = v`)
- String birleştirme (`"a" + "b"`)
- REPL: multiline + history

## Kurulum ve çalıştırma

```bash
cargo build
cargo run -- examples/hello.mb
cargo run --   # REPL
```

## Örnekler

`examples/` altında (dil özelliklerini sergiler):

| Dosya | Özellikler |
|-------|------------|
| **hello.mb** | `native::print`, temel çıktı |
| **struct_demo.mb** | struct, alan erişimi, template |
| **loop_demo.mb** | `loop`, `break`, `continue`, `if` |
| **functions.mb** | `fn`, lambda, first-class, çağrı |
| **option_match.mb** | `Maybe` enum, `match` (exhaustive) |
| **shadowing.mb** | `let` shadowing |
| **var_mutation.mb** | `var`, atama |
| **lists.mb** | list literal, index |
| **arithmetic.mb** | Int/Float, aritmetik, karşılaştırma, mantık (`&&`, `\|\|`, `!`) |
| **if_match_expr.mb** | `if` / `match` statement + expression |
| **chars_floats.mb** | `Char`, `Float` |
| **block_expr.mb** | block expression, son değer |
| **fizzbuzz.mb** | FizzBuzz (`loop`, `if`, `%`) |
| **nested_struct.mb** | iç içe struct, alan erişimi |
| **comprehensive.mb** | struct, enum, fn, lambda, match, loop, list |
| **option_result_match.mb** | `Some` / `None` / `Ok` / `Err` ile match |
| **struct_match.mb** | struct pattern match |
| **native_input.mb** | `native::input` |
| **native_debug.mb** | `native::debug` (string ve struct dahil) |
| **native_return.mb** | `native::return` (exit) |
| **return_statement.mb** | `return` statement + `Ok`/`Err` literal |
| **if_match_expr.mb** | `if` / `match` expression |
| **map_hash.mb** | `Map` (HashMap) literal |

## Teknik dokümantasyon

Ayrıntılı dil spesifikasyonu, tip sistemi ve interpreter mimarisi için:

**[docs/LANGUAGE_SPEC.md](docs/LANGUAGE_SPEC.md)**

## Proje yapısı

```
src/
  syntax_analyzer.rs — Lexer + Parser + hata raporlama
  ast.rs        — AST tanımları
  types.rs      — Tip sistemi
  value.rs      — Runtime Value
  environment.rs — Scope, binding
  native.rs     — native:: registry (print, input, return)
  interpreter.rs — AST-walking eval
  type_checker.rs — Tip denetimi (taslak)
  main.rs       — Dosya / REPL girişi
```

## Lisans

MIT.
