# Errors Examples

Bu klasör, hata mesajlarını tetiklemek için minimal örnekler içerir.

- Dosyalar prefix bazlı birleşik dosyalarda toplanır: `type_all.mb`, `runtime_all.mb`, `module_all.mb`, `syntax_all.mb`.
- Bazı örnekler özellikle TypeChecker aşamasında hata üretir (runtime’a geçmez).
- `module_unreadable.mb/` bir dizindir; `modül okunamadı` hatasını tetiklemek için kullanılır.
- Bazı hata mesajları normal kullanıcı kodundan tetiklenemez (internal). Bu tür durumlar ilgili dosyada not edilir.
