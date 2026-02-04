# Memobits

Rust ve Haskell’den ilham alan, statik tipli, tip çıkarımlı bir programlama dili. AST-walking interpreter Rust ile yazılmıştır.

Core kütüphane `no_std + alloc` uyumludur; CLI/REPL katmanı std kullanır. `no_std` modunda Map iç yapısı `BTreeMap` tabanlıdır.

## Kurulum ve çalıştırma
```bash
cargo run -- examples/simple/18_property.mb
cargo run -- examples/complex/05_validation_suite.mb
```

Performans ölçümü:
```bash
cargo run -- --performance examples/complex/05_validation_suite.mb
```

## Dokümantasyon

Tek kaynak doküman: `DOCS.md`
