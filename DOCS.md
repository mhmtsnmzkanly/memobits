# Memobits — DOCS (Agent-First)

Bu dosya `README.md` + `docs/*` içeriğinin tek yerde, agent odaklı özeti. Hızlı karar ve uygulama için önce özet, sonra ayrıntılar.

## Son Durum Özeti (Ne Yapıldı / Ne Eksik)
### Yapılanlar (Son Değişiklikler)
- `docs/` klasörü kaldırıldı; tek kaynak doküman olarak `DOCS.md` oluşturuldu.
- `README.md` sadeleştirildi ve tek kaynak olarak `DOCS.md` referans edildi. `Kurulum ve çalıştırma` bölümü bilinçli olarak boş bırakıldı.
- Hata mesajları detaylandırıldı (runtime + type checker). Mesajlar artık tip/uzunluk/arity gibi bağlam içeriyor.
- `examples/errors/` klasörü oluşturuldu ve hata örnekleri prefix bazında tek dosyada toplandı:
  - `examples/errors/type_all.mb`
  - `examples/errors/runtime_all.mb`
  - `examples/errors/module_all.mb`
  - `examples/errors/syntax_all.mb`
  - `examples/errors/module_unreadable.mb/` (modül okunamadı hatası için dizin)
- `tests/` klasörü kaldırıldı (ihtiyaç yok).

### Açık Noktalar / Yapılabilirler (Öncelikli)
1. **Hata örneklerini doğrulama**: `examples/errors/*_all.mb` içindeki her `// expected:` satırının gerçekten üretilip üretilmediğini otomatik doğrulayan bir script eklenebilir.
2. **Array literal**: `Array<T,N>` tipi ve literal sözdizimi mevcut (`@[a,b]`, `array[a,b]`, `Array(a,b)`).
3. **Kurulum/çalıştırma**: README’ye temel komutlar eklendi; istenirse genişletilebilir.
4. **Doc doğruluk notu**: Kod gerçek kaynak; doc‑code uyuşmazlığı olursa `src/` önceliklidir (mevcut).

### Dosya ve İçerik Durumu (Agent İçin)
- Tek kaynak dokümantasyon: `DOCS.md`
- Hata örnekleri: `examples/errors/*_all.mb`
- Modül yükleme hataları: `examples/errors/module_all.mb` + `examples/errors/module_unreadable.mb/`
- Syntax/lexer hataları: `examples/errors/syntax_all.mb`
- Type checker hataları: `examples/errors/type_all.mb`
- Runtime hataları: `examples/errors/runtime_all.mb`

## Hızlı Özet
- Dil: Rust + Haskell esintili, statik tipli, tip çıkarımlı.
- Runtime: AST-walking interpreter (Rust).
- Core: `no_std + alloc` uyumlu; CLI/REPL `std` kullanır.
- Heap: RC (GC yok). Stack yalnız `Value` taşır.

## Çalıştırma


## Özellikler (Güncel)
- Bloklar `{}` ile; girinti semantik değil.
- `let` (immutable) / `var` (mutable).
- `struct`, `enum`, `match` (exhaustive).
- `fn`, lambda, `native::` host entegrasyonu.
- `mod` ile modül yükleme (`mod foo;` → `foo.mb`, `mod foo from "/a/b/c/foo.mb";`).
- `if` / `else`, `loop` / `break` / `continue`, `return`.
- Option/Result benzeri hata modeli.
- String interpolasyonu (template string): `` `Merhaba {id}` `` (v1’de yalnızca `{id}`).
- `Map` indeks okuma/atama (`m[key]`, `m[key] = v`).
- String birleştirme (`"a" + "b"`).
- REPL: çok satır + geçmiş.
- Tuple (`(a, b)`), label’lı tuple tipi (`(Int label x, Int label y)`) ve `.0`/`.x` erişimi.
- Method call sugar: `p.len()` → `len(p)`.
- Primitive methods: `x.method(...)` for temel tipler desteklenir; desteklenmeyenler `unsupported primitive method` hatası verir.
- Property: `property<T> Name { Get: v => v; Set: v, input => ... } = default;`
- Type alias: `type Alias = Type;`.
- Performans ölçümü: `--performance` (load/opt/typecheck/runtime süreleri ve bellek).
- Not: `Array<T,N>` tipi ve runtime desteği var, array literal sözdizimi desteklenir.

## Sözdizimi Kısa Rehber (Gerçek Uygulama)
- Statement ayırıcı `;` (opsiyonel yerlerde parser toleranslı).
- `return;` veya `return expr;` (expr opsiyonel).
- `loop { ... }` yalnız statement; `if`/`match` hem statement hem expression.
- Atama: `x = expr` ve indeks atama: `list[i] = v`, `map[key] = v` (array indeks ataması yasak).
- Blok ifadesi: `{ stmt* }` değer üretir (son expression üzerinden).
- Map literal: `{ key => value, ... }` (ilk `=>` görünürse map; yoksa block).
- List literal: `[a, b, c]`.
- Array literal: `@[a, b, c]`, `array[a, b, c]`, `Array(a, b, c)`.
- Tuple literal: `(a, b)` ve tek elemanlı tuple: `(a,)`. Unit: `()`.
- Struct literal: `TypeName { field: expr, ... }`.
- Enum literal: `Enum::Variant` veya `Enum::Variant(expr)`.
- Option/Result literal sugar: `None`, `Some(x)`, `Ok(x)`, `Err(x)`.
- Method call sugar: `obj.m(a, b)` → `m(obj, a, b)`.
- Template string: `` `Merhaba {id}` `` yalnız identifier interpolasyonu (whitespace serbest).
- Normal string: `"..."` (escape: `\\`, `\"`, `\n`, `\r`, `\t`, `\0`).
- Char literal: `'a'` (escape: `\\`, `\'`, `\n`, `\r`, `\t`, `\0`).
- `UInt` literal: `123u` veya `123U`.
- Lambda: `x => expr` veya `a, b => expr` (param tipleri yok).
- Match pattern: `_`, literal, `ident` (binding), `Type { field: pat }`, `Enum::Variant` veya `Enum::Variant(pat)`, `Some(p)`, `Ok(p)`, `Err(p)`.

## Dil Spesifikasyonu (Kısa)
### Temel Sözdizimi
- Bloklar `{}` ile.
- Statement ayırıcı `;`.
- `let` immutable, `var` mutable.

### Tipler
- Temel: `Int`, `UInt`, `Float`, `Bool`, `Char`, `String`, `Unit`.
- Koleksiyonlar: `List<T>`, `Array<T,N>`, `Map<K,V>`.
- `Option<T>`, `Result<T,E>`.
- Tuple: `(T1, T2, ...)`.
- Label’lı tuple tipi: `(Int label x, Int label y)`.

### Fonksiyonlar
- `fn name(a: Int) -> Int { ... }`
- Lambda: `x => expr` veya `a, b => expr` (param tipleri yok).
- Method call sugar: `p.len()` → `len(p)`.
- Primitive conversion: `to_int(x)`, `to_uint(x)` (ayrıca `x.to_int()` / `x.to_uint()`).
- String methods: `chars()`, `repeat(n)`, `slice(start, len)`.

### Struct / Enum / Match
- `struct` ve `enum` tanımları.
- `match` exhaustive kontrolü (Option/Result/Enum/Bool/Unit).

### Modül Sistemi
- `mod foo;` → `foo.mb` yükler.
- `mod foo from "path";` → path ile.
- Göreli path’te `..` yasak.
- Namespace yok; tüm tanımlar global.
- `mod` adı yalnız identifier olabilir (path ayırıcı içeremez).

### String
- Template string: `` `Merhaba {name}` `` (v1’de yalnızca `{id}`).
- Normal string: `"..."` (escape: `\\`, `\"`, `\n`, `\r`, `\t`, `\0`).
- `UInt` literal: `123u` veya `123U`.

## Bellek Mimarisi
### Özet
- Stack yalnız `Value` taşır.
- Heap yalnız `HeapObject` taşır.
- Heap nesneleri `Rc` ile yönetilir (GC yok).

### Value
```rust
Value::Int | UInt | Float | Bool | Char | Unit | HeapRef(Rc<HeapObject>)
```

### HeapObject
- String
- Struct { type_id, fields }
- Enum { type_id, variant_id, payload }
- Tuple { labels, values }
- List(Vec<Value>)
- Array(Vec<Value>)
- Map(HashMap<Value, Value>) (std) / Map(BTreeMap<Value, Value>) (no_std)
- Closure { fn_id, env }

### Closure
- Capture: `EnvRef = Rc<HashMap<String, Value>>`
- Closure immutable capture.

### no_std Notu
- `no_std` modunda `Map` `BTreeMap` tabanlıdır.

## Runtime Kısıtları ve Notlar
- Map key’leri yalnız `Int/UInt/Bool/Char/String` olabilir (aksi runtime error).
- Array indeks ataması desteklenmez (`list`/`map` için destek var).
- Tuple label’ları yalnızca type annotation üzerinden uygulanır; literal tuple label üretmez.
- `native::` fonksiyonları (std): `print`, `debug`, `input`, `return`. `no_std` modunda registry boş başlar.
- Expression bloklarında `break`/`continue`/`return` kullanımı runtime error üretir.

## Compile‑Time (TypeChecker)
- Tip çıkarımı / doğrulama.
- Const‑eval (aritmetik, bool, string concat).
- Const error:
  - `1/0`, `1%0`
  - array/list index OOB
  - map key not found (const) artık runtime’a bırakılır (hard‑error değil)
- `if`/`match` sabit koşulda sadece erişilebilir branch kontrol edilir.
- Exhaustiveness: `Option`, `Result`, `Enum`, `Bool`, `Unit`.

## Örnekler
- `examples/simple/` → her özellik için kısa örnekler.
- `examples/complex/` → birleşik senaryolar.
- `examples/complex/05_validation_suite.mb` → tek dosyada kapsamlı doğrulama.
- `examples/errors/` → hata mesajı örnekleri (tek dosyada birleşik).

## Dil Sözdizimi Örnekleri
```mb
// let / var
let x = 10;
var y = x + 5;

// fn + return
fn add(a: Int, b: Int) -> Int { return a + b; }

// tuple + access
let p = (1, 2);
let first = p.0;

// struct + enum
struct Point { x: Int, y: Int }
enum Color { Red, Rgb(Int) }
let c = Color::Rgb(255);

// map + list + template
let m = { "a" => 1, "b" => 2 };
let l = [1, 2, 3];
let msg = `len {x}`;
```

## Yol Haritası (Yakın Gelecek)
- Exhaustiveness için tuple/struct pattern coverage.
- Daha agresif const‑eval (tuple index const check vb.).
- Daha iyi hata mesajları (span iyileştirme).
- AST → bytecode VM (performans).
- Field index cache / hot path optimizasyonları.
- Modül sistemi: namespace (`foo::bar`), `use`/`pub` erişim kontrolü.
- Dil özellikleri: Ownership/borrow modeli, user‑defined generics.

## Değişim Notları (Kısa Özet)
- examples klasörü tamamen yenilendi (simple/complex).
- Tuple + label tipi eklendi.
- Method call sugar eklendi: `p.len()` → `len(p)`.
- Type alias eklendi.
- Modül sistemi: `mod foo from "path";` + `..` yasak.
- Bellek modeli RC‑heap ile yeniden kurgulandı.
- `no_std + alloc` core uyumu.
- Compile‑time const‑eval genişletildi (list/map/tuple literal).
- Exhaustiveness: Bool/Unit eklendi.

## Doğruluk Notu
- Bu doküman, kodun mevcut davranışını yansıtmayı hedefler; gerçek kaynak her zaman koddur.
- Şüpheli/çelişkili bir noktada öncelik `src/` altındaki implementasyondadır.

## Proje Yapısı
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

examples/
  simple/   — her özellik için kısa örnekler
  complex/  — birleşik senaryolar
  errors/   — hata mesajı örnekleri
    type_all.mb    — type checker hataları
    runtime_all.mb — runtime hataları
    module_all.mb  — modül yükleme hataları
    syntax_all.mb  — lexer/parser hataları
    module_unreadable.mb/ — modül okunamadı hatası için dizin

```

## Lisans
MIT.
