# Memobits — Teknik Dil Spesifikasyonu

Bu belge, **Memobits** programlama dilinin tasarımı, sözdizimi, tip sistemi ve Rust ile yazılmış AST-walking interpreter mimarisini tanımlar.

---

## 1. Dilin Felsefesi ve Tasarım Gerekçeleri

### 1.1 Amaç

Memobits, **genel amaçlı**, **statik tipli** ve **tip çıkarımlı** bir dildir. Oyuncak bir dil olmaktan çok, sade ama **genişletilebilir** bir temel sunar. Rust’ın güvenli mutability modeli ve Haskell’in ifade odaklı, fonksiyonel yaklaşımından ilham alır.

### 1.2 Temel İlkeler

- **Bloklar `{}` ile tanımlanır.** İndentation semantik değildir; sözdizimi tamamen ayraçlara dayanır. Bu, farklı editörler ve platformlarda tutarlı davranış sağlar.
- **Her şey fonksiyon olarak kabul edilir.** İsimli fonksiyonlar, isimsiz fonksiyonlar ve lambda’lar first-class değerlerdir. Kontrol akışı (if/else, loop) statement olarak kalır; ileride expression formları eklenebilir.
- **Statik tip sistemi, tip çıkarımı ile.** Programcı gerektiğinde açık tip yazar; gereksiz tekrar önlenir. Tip uyuşmazlığında **derleme/çözümleme hatası** verilir; otomatik type promotion yoktur.
- **Mutability binding seviyesinde.** `let` ile immutable, `var` ile mutable binding. Struct/enum içinde field bazlı `mut` yok; v1 sadece binding seviyesinde mutability sunar.
- **Değer semantiği varsayılan.** Koleksiyonlar interpreter içinde paylaşılan immutable referanslarla tutulur; `var` ile kontrollü mutasyon yapılır. v1’de GC yok; `Rc` ve environment zinciri kullanılır.

### 1.3 Rust / Haskell Etkileri

| Kaynak | Etki |
|--------|------|
| **Rust** | `let`/`var`, struct/enum, `match`, exhaustive matching, `Option`/`Result` benzeri hata modeli, nominal type system, `native::` namespace |
| **Haskell** | Fonksiyonların first-class oluşu, tip çıkarımı, expression odaklılık (fonksiyon tarafında), sade veri yapıları |

### 1.4 v1 Kapsamı

- Lexer, Parser, AST, tip çıkarımı/doğrulama, AST-walking interpreter.
- Temel tipler, struct, enum, match, fonksiyonlar (isimli, isimsiz, lambda), `if`/`else`, `loop`/`break`/`continue`.
- `Option<T>`, `Result<T,E>` benzeri yapılar ve hata durumunda execution’ın durması.
- `native::` ile host fonksiyonları (print, input, vs.).

---

## 2. Sözdizimi Kuralları

### 2.1 Genel Notasyon

- **Küçük harf duyarlı.** `Foo` ile `foo` farklı tanımlayıcılardır.
- **Bloklar** her zaman `{` … `}` ile sınırlanır.
- **Noktalı virgül** expression/statement ayırıcı olarak kullanılır; blok sonu hariç gerektiğinde infer edilebilir (opsiyonel kural, implementasyona bırakılır).

### 2.2 Tanımlayıcılar ve Anahtar Sözcükler

**Anahtar sözcükler:** `let`, `var`, `fn`, `struct`, `enum`, `match`, `if`, `else`, `loop`, `break`, `continue`, `true`, `false`, `nil`, `Option`, `Result`, `Ok`, `Err`, `Some`, `None`, `Array`, `List`, `Map`, `Int`, `Float`, `Bool`, `Char`, `String`, `native`.

Tanımlayıcılar harf veya `_` ile başlar; harf, rakam, `_` içerebilir.

### 2.3 Temel Tipler ve Literaller

```
Int:    42, 0, -7
Float:  3.14, 0.0, -1.5e2
Bool:   true, false
Char:   'a', '\n', '\''
String: "hello", `Merhaba {name}`  // interpolasyon backtick ile
```

String interpolasyonu sadece **backtick** (\`) string’lerde geçerlidir; `"..."` içinde yoktur. v1’de yalnızca `{id}` (basit tanımlayıcı) desteklenir; `{expr}` veya `{obj.field}` yoktur.

### 2.4 Değişkenler ve Mutability

```memobits
let x = 10;           // immutable, shadowing serbest
let x = 20;           // yeni binding, önceki gölgelenir

var counter = 0;      // mutable
counter = counter + 1;
```

- **Shadowing:** Aynı isimde yeni `let` binding’e izin verilir.
- **`var`:** Sadece atama ile değiştirilebilir; tip sabit kalır.

### 2.5 Struct

```memobits
struct Player {
    name: String,
    points: Int
}

let p = Player { name: "Alice", points: 100 };
let name = p.name;
```

Struct’lar **saf veri** yapılarıdır; method yok. Nominal type system: isim eşleşmesi gerekir.

### 2.6 Enum ve Match

```memobits
enum Maybe {
    Nothing,
    Just(Int)
}

let m = Maybe::Just(42);
match m {
    Maybe::Nothing => native::print("yok"),
    Maybe::Just(x) => native::print(`sayi: {x}`)
}
```

- **Exhaustive match zorunlu.** Tüm variant’lar karşılanmalı.
- **`_` wildcard** opsiyonel; kullanılırsa “geri kalan” her şeyi yakalar.

### 2.7 Fonksiyonlar

**İsimli fonksiyon:** Parametre ve dönüş tipi zorunlu.

```memobits
fn add(a: Int, b: Int) -> Int {
    a + b
}

fn say_hello(name: String) -> String {
    `Merhaba {name}`
}
```

**Lambda:** Tamamen tip çıkarımlı. Tip gerekirse annotasyon ile verilir.

```memobits
let double: fn(Int) -> Int = x => x * 2;

let say_hi: fn(String) -> String = name => `Hi {name}`;
```

**İsimsiz fonksiyon:** Lambda’ya atanabilir veya argüman olarak geçirilebilir (first-class).

### 2.8 Kontrol Yapıları

**if / else (statement):**

```memobits
if x > 0 {
    native::print("pozitif");
} else {
    native::print("negatif veya sıfır");
}
```

**loop, break, continue:**

```memobits
var i = 0;
loop {
    if i >= 10 { break; }
    if i % 2 == 0 { i = i + 1; continue; }
    native::print(`{i}`);
    i = i + 1;
}
```

### 2.9 Koleksiyonlar

```memobits
let arr: Array<Int, 3> = [1, 2, 3];
let lst: List<String> = ["a", "b", "c"];
let m: Map<String, Int> = {"x" => 1, "y" => 2};
```

- **Array<T, N>:** Sabit boyut, derleme zamanında bilinir.
- **List<T>:** Dinamik boyut; `push`, `pop` vb. native veya built-in ile.
- **Map<K, V>:** K ve V tipleri önceden belirtilir. İterasyon: **insertion order** (v1’de tutarlı tek seçenek).

### 2.10 Hata Modeli: Option ve Result

```memobits
let o: Option<Int> = Some(42);
match o {
    None => native::print("yok"),
    Some(v) => native::print(`var: {v}`)
}

let r: Result<Int, String> = Ok(10);
match r {
    Err(e) => native::print(`hata: {e}`),
    Ok(v)  => native::print(`deger: {v}`)
}
```

Hata oluştuğunda (ör. `Err` match edilmeden kullanım, panic benzeri durum) **execution durur**.

### 2.11 Native / Host Entegrasyonu

Tüm host fonksiyonları **`native::`** altında tanımlanır. Interpreter başlatılırken register edilir.

```memobits
native::print("hello");
let s = native::input();
let _ = native::return(0);
```

Örnek imzalar (semantik):

- `native::print(x: String) -> ()`
- `native::input() -> String`
- `native::return(code: Int) -> Never` (programı sonlandırır)

### 2.12 Örnek Tam Program

```memobits
struct Player { name: String, score: Int }

fn greet(p: Player) -> String {
    `Player {p.name} has score {p.score}`
}

fn main() -> () {
    let p = Player { name: "Alice", score: 100 };
    let msg = greet(p);
    native::print(msg);
}
```

---

## 3. Tip Sistemi Detayları

### 3.1 Statik ve Tip Çıkarımlı

- Tüm ifadelerin tipi **derleme/çözümleme** aşamasında bilinir.
- Açık annotasyon zorunlu değildir; çıkarılamadığında veya okunabilirlik için kullanılır.
- **Tip uyuşmazlığı** → analiz hatası, çalıştırma yok.

### 3.2 Temel Tipler

| Tip | Açıklama |
|-----|----------|
| `Int` | Sabit genişlik tam sayı (Rust `i64` veya benzeri) |
| `Float` | IEEE 754 (Rust `f64`) |
| `Bool` | `true` / `false` |
| `Char` | Tek Unicode scalar |
| `String` | UTF-8, Rust `String` üzerine |

### 3.3 Equality ve Karşılaştırma

- **Primitive:** Değer bazlı (`==`, `!=`, `<`, `<=`, `>`, `>=`).
- **Struct:** Alan alan (field-by-field) karşılaştırma.
- **Enum:** Variant + içerik bazlı.

Tip uyuşmazlığında (ör. `Int` ile `String` karşılaştırma) analiz hatası.

### 3.4 Fonksiyon Tipleri

`fn(T1, T2, ...) -> R` şeklinde temsil edilir. Lambda’lar aynı tip yapısına sahiptir; parametre ve dönüş tipleri çıkarım veya annotasyonla belirlenir.

### 3.5 Generic’ler (v1)

v1’de tam generic sistem yok; `Option<T>`, `Result<T,E>`, `List<T>`, `Array<T,N>`, `Map<K,V>` dil tarafından tanımlı “hazır” generic’ler olarak ele alınır. İleride kullanıcı tanımlı generic struct/enum eklenebilir.

---

## 4. Struct, Enum ve Match

### 4.1 Struct

- **Rust-vari** named-field struct.
- **Nominal:** Aynı alan yapısına sahip iki struct, isimleri farklıysa farklı tiplerdir.
- **Method yok;** sadece veri taşır. Davranış fonksiyonlarla verilir.

### 4.2 Enum

- **Rust-style:** Variant + opsiyonel veri.
- Örnekler: `Maybe::Nothing`, `Maybe::Just(Int)`, `Result::Ok(T)`, `Result::Err(E)`.

### 4.3 Match

- **Expression** değil **statement** (veya v1’de expression olarak da kullanılabilir; tutarlılık önemli).
- **Exhaustive:** Tüm variant’lar ele alınmalı.
- **`_`** opsiyonel; kullanılırsa diğer pattern’leri karşılar.
- Pattern sırası önemli değildir; semantik exhaustive’lık önemlidir.

---

## 5. Interpreter Mimarisi

### 5.1 Genel Akış

```
Kaynak kod → Lexer → Token akışı → Parser → AST → Tip analizi → AST-walking Interpreter → Sonuç
```

### 5.2 Lexer

- **Girdi:** Kaynak metin (UTF-8).
- **Çıktı:** Token akışı (keyword, identifier, literal, operatör, ayraç, vb.).
- **Kurallar:** Sayılar, string’ler (çift tırnak ve backtick), karakterler, yorumlar (ör. `//`) ve boşluklar için net kurallar.

### 5.3 Parser

- **Girdi:** Token akışı.
- **Çıktı:** Soyut sözdizim ağacı (AST).
- **Yöntem:** Recursive descent veya benzeri; öncelik ve ilişkilendirme kurallarına uygun expression parsing.

### 5.4 AST

- **Program** → tanım listesi (struct, enum, fn, global let/var) + opsiyonel `main` veya giriş noktası.
- **Expression:** literal, ident, binary/unary op, call, block, if, loop, match, lambda.
- **Statement:** let, var, assign, if, loop, match, expression-statement.

### 5.5 Environment

- **Scope zinciri:** Her blok yeni bir scope açar; üst scope’lar zincirleme erişilebilir.
- **Binding’ler:** `let` / `var` ile isim → `Value` (ve mutability bilgisi).
- **Rc** ile paylaşılan değerler (koleksiyonlar, struct içinde referans vb.); v1’de GC yok.

### 5.6 Tip Analizi

- AST üzerinde tek geçiş (veya gerekirse çoklu): tip çıkarımı + doğrulama.
- Uyuşmazlıkta hata üretilir; başarılıysa AST tip bilgisiyle zenginleştirilir (veya ayrı bir harita tutulur).

---

## 6. Rust Tarafı: AST ve Interpreter Modeli

### 6.1 Modül Yapısı

```
memobits/
├── src/
│   ├── main.rs       // REPL veya dosya çalıştırma
│   ├── lib.rs        // modül root
│   ├── lexer.rs      // token, lexer
│   ├── parser.rs     // parser, AST üretimi
│   ├── ast.rs        // AST node tanımları
│   ├── types.rs      // Type enum (Int, Float, …, fn, struct, enum)
│   ├── value.rs      // Runtime Value (Int, Float, …)
│   ├── environment.rs // Scope, binding, Rc
│   ├── interpreter.rs // AST-walking eval
│   └── native.rs     // native:: kayıt ve çağrı
```

### 6.2 AST Enum (Özet)

```rust
pub enum Expr {
    Literal(Literal),
    Ident(String),
    Binary { op: BinOp, left: Box<Expr>, right: Box<Expr> },
    Unary { op: UnaryOp, inner: Box<Expr> },
    Call { callee: Box<Expr>, args: Vec<Expr> },
    Block(Vec<Stmt>),
    If { cond: Box<Expr>, then_b: Vec<Stmt>, else_b: Option<Vec<Stmt>> },
    Loop(Vec<Stmt>),
    Match { scrutinee: Box<Expr>, arms: Vec<MatchArm> },
    Lambda { params: Vec<(String, Type)> /* infer */, body: Box<Expr> },
    StructLiteral { name: String, fields: Vec<(String, Expr)> },
    ListLiteral(Vec<Expr>),
    ArrayLiteral(Vec<Expr>),
    MapLiteral(Vec<(Expr, Expr)>),
}

pub enum Stmt {
    Let { name: String, typ: Option<Type>, init: Expr },
    Var { name: String, typ: Option<Type>, init: Expr },
    Assign { name: String, value: Expr },
    Expr(Expr),
    Break,
    Continue,
}
```

`MatchArm`, `Literal`, `BinOp`, `UnaryOp`, `Type` ayrı tanımlanır; `Type` ile `types.rs` uyumlu olur.

### 6.3 Value (Runtime)

```rust
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    String(Rc<str>),
    Option(Option<Box<Value>>),
    Result(Result<Box<Value>, Box<Value>>),
    Struct { name: String, fields: HashMap<String, Value> },
    Variant { name: String, variant: String, data: Option<Box<Value>> },
    List(Rc<RefCell<Vec<Value>>>),
    Array(Rc<[Value]>),
    Map(Rc<RefCell<Vec<(Value, Value)>>>),  // insertion order
    Function(NativeFn),
    Lambda(LambdaClosure),
}
```

`NativeFn` ve `LambdaClosure` interpreter’ın çağırabileceği şekilde tanımlanır.

### 6.4 Interpreter Yürütme Modeli

- **Girdi:** Tip analizinden geçmiş AST (veya analiz interpreter içinde).
- **Yöntem:** AST üzerinde recursive walk; her `Expr` ve `Stmt` için `eval`/`execute`.
- **Environment:** Her blok girişinde yeni scope, çıkışta pop. `let`/`var` binding’ler burada tutulur.
- **Kontrol akışı:** `break`/`continue` için kullanılan bir kontrol flag’i veya `Result`-benzeri early-return (internal).
- **Native çağrılar:** `callee` bir `native::` path’i çözümlenince `native::` registry’den fonksiyon alınır ve çağrılır.

### 6.5 Native Kayıt

- `native::print`, `native::input`, `native::return` vb. interpreter başlatılırken `native::register("print", fn(...))` benzeri bir API ile eklenir.
- Çözümleme sırasında `native::X` → bu registry’den lookup; bulunamazsa analiz hatası.

---

## 7. v1 Kapsam Dışı ve Gelecek Genişlemeler

### 7.1 v1’de Olmayanlar

- **GC:** Sadece Rc + environment; döngüsel referans yönetilmez.
- **Field-level mut:** Struct alanları ayrı ayrı `mut` değil.
- **Modül / import:** Tek dosya; `use`/`mod` yok.
- **Generic kullanıcı tanımlı:** Sadece built-in generic tipler.
- **Trait / typeclass:** Yok.
- **Macro:** Yok.
- **Concurrency:** Yok.

### 7.2 Gelecek Adımlar

- **Modül sistemi:** Dosya bazlı modüller, `use`, `pub`.
- **Trait benzeri arayüzler:** Ad-hoc polymorphism, impl blokları.
- **Daha zengin generic’ler:** Kullanıcı tanımlı generic struct/enum/fn.
- **`?` operatörü:** Result propagation.
- **Closure capture kuralları:** Açık capture listesi veya borrow semantiği.
- **JIT / bytecode:** AST yerine bytecode ile çalıştırma.
- **Debugger / REPL iyileştirmeleri:** Adım adım çalıştırma, breakpoint.

---

Bu spesifikasyon, Memobits v1 interpreter’ının referans dokümanıdır. Uygulama buraya uygun ilerletilir; tutarsızlık durumunda belge güncellenir.
