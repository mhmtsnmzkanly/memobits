# Memobits — Teknik Dil Spesifikasyonu

Bu belge, **Memobits** programlama dilinin tasarımı, sözdizimi, tip sistemi ve Rust ile yazılmış AST-walking interpreter mimarisini tanımlar.

---

## 1. Dilin Felsefesi ve Tasarım Gerekçeleri

### 1.1 Amaç

Memobits, **genel amaçlı**, **statik tipli** ve **tip çıkarımlı** bir dildir. Oyuncak bir dil olmaktan çok, sade ama **genişletilebilir** bir temel sunar. Rust’ın güvenli mutability modeli ve Haskell’in ifade odaklı yaklaşımından ilham alır.

### 1.2 Temel İlkeler

- **Bloklar `{}` ile tanımlanır.** Indentation semantik değildir.
- **Fonksiyonlar ve lambda’lar first-class** değerlerdir.
- **Statik tip sistemi, tip çıkarımı ile.** Tip uyuşmazlığında analiz hatası verir.
- **Mutability binding seviyesinde.** `let` immutable, `var` mutable.
- **Değer semantiği varsayılan.** Koleksiyonlar `Rc`/`RefCell` ile paylaşılır.

### 1.3 Rust / Haskell Etkileri

| Kaynak | Etki |
|--------|------|
| **Rust** | `let`/`var`, struct/enum, `match`, `Option`/`Result`, `native::` namespace |
| **Haskell** | expression odaklılık, tip çıkarımı, fonksiyonların first-class oluşu |

### 1.4 v1 Kapsamı

- **SyntaxAnalyzer** (lexer + parser) → AST
- **TypeChecker** (taslak): tip çıkarımı/doğrulama
- **AST-walking interpreter**
- Temel tipler, struct, enum, match, fonksiyonlar, `if`/`else`, `loop`/`break`/`continue`, `return`
- `Option<T>`, `Result<T,E>` benzeri yapılar
- `native::` host fonksiyonları (print, input, debug, return)

---

## 2. Sözdizimi Kuralları

### 2.1 Genel Notasyon

- **Küçük harf duyarlı.** `Foo` ile `foo` farklıdır.
- **Bloklar** `{` … `}` ile sınırlandırılır.
- **Noktalı virgül** statement ayırıcıdır; blok sonunda opsiyoneldir.

### 2.2 Anahtar Sözcükler

`let`, `var`, `fn`, `struct`, `enum`, `match`, `if`, `else`, `loop`, `break`, `continue`, `return`,
`true`, `false`, `Option`, `Result`, `Ok`, `Err`, `Some`, `None`, `Array`, `List`, `Map`,
`Int`, `Float`, `Bool`, `Char`, `String`, `native`.

### 2.3 Temel Tipler ve Literaller

```
Int:    42, 0, -7
Float:  3.14, 0.0, -1.5e2
Bool:   true, false
Char:   'a', '\n', '\''
String: "hello", `Merhaba {name}`
```

- **String interpolasyonu** yalnızca backtick (
```
`
```
) string’lerde geçerlidir.
- v1’de interpolasyon sadece `{id}` biçimindedir.
- **String birleştirme** `+` ile yapılabilir: `"a" + "b"`.

### 2.4 Değişkenler ve Mutability

```memobits
let x = 10;           // immutable
let x = 20;           // shadowing

var counter = 0;      // mutable
counter = counter + 1;
```

### 2.5 Struct

```memobits
struct Player {
    name: String,
    points: Int
}

let p = Player { name: "Alice", points: 100 };
let name = p.name;
```

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

- **Exhaustive match** zorunludur.
- `_` wildcard kullanılabilir.
- `Some/None` ve `Ok/Err` pattern’leri desteklenir.
- v1 sınırlaması: `match` scrutinee içinde **struct literal** doğrudan kullanılamaz.
  - Çözüm: önce `let tmp = Type { ... };` sonra `match tmp { ... }`,
    **veya** parantez içinde yaz: `match (Type { ... }) { ... }`.

### 2.7 Fonksiyonlar ve Return

```memobits
fn add(a: Int, b: Int) -> Int {
    return a + b;
}

fn greet(name: String) -> String {
    `Merhaba {name}`
}
```

- `return expr;` desteklenir. `return;` → `()` döner.
- **Lambda** v1’de tek parametreli: `x => expr`.

### 2.8 Kontrol Yapıları (Statement ve Expression)

**if / else expression olarak kullanılabilir:**

```memobits
let label = if (x % 2 == 0) { "even" } else { "odd" };
```

- `if` statement, doğrudan değer döndürmez. Değer gerekiyorsa `let` ile alınmalı veya `return` kullanılmalıdır.

**match expression olarak kullanılabilir:**

```memobits
let v = Some(3);
let doubled = match v {
    None => 0,
    Some(n) => (n * 2)
};
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

- **Array<T, N>:** sabit boyut.
- **List<T>:** dinamik boyut.
- **Map<K, V>:** runtime’da HashMap. v1’de **key tipi sınırlı**: `Int`, `Bool`, `Char`, `String`.
- **Map index:** `m["x"]` ile okuma, `m["x"] = 2` ile güncelleme.
- **Map literal / Block ayrımı:** Expression bağlamında `{ key => value }` map literal, statement/if/match gövdelerinde `{ ... }` block olarak yorumlanır.

### 2.12 Compile-Time Güvenlik (v1)

- **Sabit ifadeler** compile-time'da değerlendirilebilir.
- **Bölme/Mod**: `1 / 0` ve `1 % 0` gibi sabit ifadeler compile-time error.
- **Array index**: sabit index out-of-bounds ise compile-time error.
- **Ulaşılamayan kod**: `return` sonrası ifadeler compile-time warning (satır/sütun ile).

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

### 2.11 Native / Host Entegrasyonu

```memobits
native::print("hello");
let s = native::input();
let _ = native::return(0);
```

- `native::return` programdan çıkış için kullanılır.
- `native::debug` ham runtime değerleri yazdırır.

---

## 3. Tip Sistemi Detayları

### 3.1 Statik ve Tip Çıkarımlı

- Tüm ifadeler için tip çıkarımı yapılır.
- TypeChecker **taslak** durumundadır: bazı durumlarda `Unknown` kullanılır.
- Tip uyuşmazlığında analiz hatası üretilir.

### 3.2 Temel Tipler

| Tip | Açıklama |
|-----|----------|
| `Int` | i64 |
| `Float` | f64 |
| `Bool` | `true/false` |
| `Char` | Unicode char |
| `String` | UTF-8 |

### 3.3 Equality ve Karşılaştırma

- **Primitive:** Değer bazlı.
- **Struct/Enum:** v1’de runtime karşılaştırma sınırlı; tip denetimi yapılır.

### 3.4 Fonksiyon Tipleri

`fn(T1, T2, ...) -> R` şeklinde temsil edilir.

### 3.5 Generic’ler (v1)

`Option<T>`, `Result<T,E>`, `List<T>`, `Array<T,N>`, `Map<K,V>` hazır generic tipler olarak ele alınır.

---

## 4. Struct, Enum ve Match

### 4.1 Struct

- Nominal tip sistemi.
- Field kontrolü: literal ve pattern’lerde alan doğrulaması yapılır.

### 4.2 Enum

- Rust-style variant + opsiyonel veri.
- `Option`/`Result` runtime’da **Variant** olarak temsil edilir.

### 4.3 Match

- Statement veya expression olarak kullanılabilir.
- **Exhaustive** olması beklenir; TypeChecker basit kontrol uygular.
- Pattern kapsamı: literal, `_`, `None/Some`, `Ok/Err`, `Enum::Variant`.
- v1 sınırlaması: `match` scrutinee içinde **struct literal** doğrudan kullanılamaz.

---

## 5. Interpreter Mimarisi

### 5.1 Genel Akış

```
Kaynak kod → SyntaxAnalyzer (lexer+parser) → AST → Tip analizi → Interpreter
```

### 5.2 SyntaxAnalyzer

- Logos tabanlı lexer.
- Recursive descent parser.
- Span’lar ve hata konumları üretilir.

### 5.3 AST

- Program: struct/enum/fn/global let/var + top-level statement.
- Expression: literal, ident, binary/unary, call, block, if, match, lambda, struct/variant, list/array/map, template.
- Statement: let, var, assign, if, loop, match, return, break, continue.

### 5.4 Environment

- Scope zinciri.
- `let`/`var` binding’ler; mutable flag.

### 5.5 Runtime Value

- Primitive + struct/variant + list/array/map.
- `Option/Result` runtime’da `Variant` olarak temsil edilir.
- Map, `HashMap<MapKey, Value>`; `MapKey` yalnızca `Int/Bool/Char/String`.

---

## 6. Rust Tarafı: Modül Yapısı

```
memobits/
├── src/
│   ├── main.rs          // REPL veya dosya çalıştırma
│   ├── lib.rs           // modül root
│   ├── syntax_analyzer.rs // lexer + parser
│   ├── ast.rs           // AST node tanımları
│   ├── types.rs         // Type enum
│   ├── value.rs         // Runtime Value
│   ├── environment.rs   // Scope, binding, Rc
│   ├── interpreter.rs   // AST-walking eval
│   ├── native.rs        // native:: kayıt ve çağrı
│   └── type_checker.rs  // Tip denetimi (taslak)
```

---

## 7. v1 Kapsam Dışı ve Gelecek Genişlemeler

- Modül sistemi
- Kullanıcı tanımlı generic’ler
- Trait/typeclass
- `?` operatörü
- Gelişmiş REPL (multi-line, history)
- Bytecode/JIT

---

Bu spesifikasyon, Memobits v1 interpreter’ının referans dokümanıdır. Uygulama geliştikçe güncellenir.
