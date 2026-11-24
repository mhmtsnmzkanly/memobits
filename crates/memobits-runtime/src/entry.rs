use memobits_entry_abi::{Family, Metadata, Scalar, ERROR_ID_BYTES, RESULT_ALIGNMENT};
use std::fmt;

use crate::RunError;

/// A primitive success payload decoded using its source type.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EntrySuccess {
    Bool(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    F32(f32),
    F64(f64),
}

impl fmt::Display for EntrySuccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(value) => write!(f, "bool({value})"),
            Self::I8(value) => write!(f, "i8({value})"),
            Self::I16(value) => write!(f, "i16({value})"),
            Self::I32(value) => write!(f, "i32({value})"),
            Self::I64(value) => write!(f, "i64({value})"),
            Self::U8(value) => write!(f, "u8({value})"),
            Self::U16(value) => write!(f, "u16({value})"),
            Self::U32(value) => write!(f, "u32({value})"),
            Self::U64(value) => write!(f, "u64({value})"),
            Self::F32(value) => write!(f, "f32({value:?})"),
            Self::F64(value) => write!(f, "f64({value:?})"),
        }
    }
}

/// The host-visible part of a returned error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedError {
    pub type_name: String,
    pub code: u32,
}

/// A normal return from a compiler-known outcome entry: `T ! E` returns `Ok`
/// or `Err`; `T ?! E` (`Result<Option<T>, E>`) returns `OkSome`, `OkNone` or `Err`.
#[derive(Clone, Debug, PartialEq)]
pub enum EntryOutcome {
    Ok(EntrySuccess),
    OkSome(EntrySuccess),
    OkNone,
    Err(ReturnedError),
}

impl fmt::Display for EntryOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ok(value) => write!(f, "Ok({value})"),
            Self::OkSome(value) => write!(f, "Ok(Some({value}))"),
            Self::OkNone => f.write_str("Ok(None)"),
            Self::Err(error) => write!(f, "Err({}, code={})", error.type_name, error.code),
        }
    }
}

pub(crate) fn decode(
    metadata: Metadata<'_>,
    memory: &[u8],
    address: u32,
    size: u32,
) -> Result<EntryOutcome, RunError> {
    if size != metadata.size {
        return Err(invalid("returned size differs from entry metadata"));
    }
    if address < RESULT_ALIGNMENT || !address.is_multiple_of(RESULT_ALIGNMENT) {
        return Err(invalid("unaligned or reserved entry result address"));
    }
    let result = address
        .checked_add(size)
        .and_then(|end| memory.get(address as usize..end as usize))
        .ok_or_else(|| invalid("entry result is outside guest memory"))?;
    let payload = &result[usize::from(metadata.payload_offset)..];
    match (metadata.family, result[0]) {
        (Family::Result, 0) => Ok(EntryOutcome::Ok(read_success(metadata.success, payload)?)),
        (Family::OptionalResult, 0) => match payload[0] {
            0 => Ok(EntryOutcome::OkSome(read_success(
                metadata.success,
                &payload[usize::from(metadata.inner_offset)..],
            )?)),
            1 => Ok(EntryOutcome::OkNone),
            _ => Err(invalid("unknown optional tag")),
        },
        (_, 1) => {
            let (identity, code) = payload.split_at(ERROR_ID_BYTES as usize);
            let identity = u32::from_le_bytes(identity.try_into().expect("four identity bytes"));
            if identity != metadata.error_id {
                return Err(invalid("unrecognized concrete error identity"));
            }
            Ok(EntryOutcome::Err(ReturnedError {
                type_name: metadata.error_name.to_owned(),
                code: u32::from_le_bytes(code[..4].try_into().expect("validated payload size")),
            }))
        }
        _ => Err(invalid("unknown entry outcome tag")),
    }
}

fn read_success(kind: Scalar, payload: &[u8]) -> Result<EntrySuccess, RunError> {
    let payload = &payload[..kind.width() as usize];
    Ok(match kind {
        Scalar::Bool => EntrySuccess::Bool(match payload[0] {
            0 => false,
            1 => true,
            _ => return Err(invalid("invalid bool success payload")),
        }),
        Scalar::I8 => EntrySuccess::I8(payload[0] as i8),
        Scalar::U8 => EntrySuccess::U8(payload[0]),
        Scalar::I16 => EntrySuccess::I16(i16::from_le_bytes(payload.try_into().unwrap())),
        Scalar::U16 => EntrySuccess::U16(u16::from_le_bytes(payload.try_into().unwrap())),
        Scalar::I32 => EntrySuccess::I32(i32::from_le_bytes(payload.try_into().unwrap())),
        Scalar::U32 => EntrySuccess::U32(u32::from_le_bytes(payload.try_into().unwrap())),
        Scalar::F32 => EntrySuccess::F32(f32::from_le_bytes(payload.try_into().unwrap())),
        Scalar::I64 => EntrySuccess::I64(i64::from_le_bytes(payload.try_into().unwrap())),
        Scalar::U64 => EntrySuccess::U64(u64::from_le_bytes(payload.try_into().unwrap())),
        Scalar::F64 => EntrySuccess::F64(f64::from_le_bytes(payload.try_into().unwrap())),
    })
}

pub(crate) fn invalid(message: &str) -> RunError {
    RunError::EntryAbi(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{run, with_custom_section};
    use memobits_entry_abi::{ENTRY_EXPORT, MEMORY_EXPORT, SECTION};
    use wasm_encoder::{
        CodeSection, ConstExpr, DataSection, ExportKind, ExportSection, Function, FunctionSection,
        Instruction, MemorySection, MemoryType, Module, TypeSection, ValType,
    };

    fn metadata() -> Vec<u8> {
        Metadata {
            family: Family::Result,
            success: Scalar::Bool,
            payload_offset: 4,
            inner_offset: 0,
            size: 12,
            error_id: 1,
            error_name: "pkg::mod::ErrorType",
        }
        .encode()
        .unwrap()
    }

    fn guest(address: u32, size: u32, result: [u8; 12], export_memory: bool) -> Vec<u8> {
        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], [ValType::I32, ValType::I32]);
        let mut functions = FunctionSection::new();
        functions.function(0);
        let mut memories = MemorySection::new();
        memories.memory(MemoryType {
            minimum: 1,
            maximum: Some(1),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        let mut exports = ExportSection::new();
        exports.export(ENTRY_EXPORT, ExportKind::Func, 0);
        if export_memory {
            exports.export(MEMORY_EXPORT, ExportKind::Memory, 0);
        }
        let mut code = CodeSection::new();
        let mut adapter = Function::new([]);
        adapter
            .instruction(&Instruction::I32Const(address as i32))
            .instruction(&Instruction::I32Const(size as i32))
            .instruction(&Instruction::End);
        code.function(&adapter);
        let mut data = DataSection::new();
        data.active(0, &ConstExpr::i32_const(16), result);
        module
            .section(&types)
            .section(&functions)
            .section(&memories)
            .section(&exports)
            .section(&code)
            .section(&data);
        module.finish()
    }

    #[test]
    fn validates_entry_metadata_before_reading_guest_results() {
        let module = guest(16, 12, [0; 12], true);
        let valid = metadata();
        let attach = |bytes: &[u8]| with_custom_section(&module, SECTION, bytes);
        assert_eq!(
            run(&attach(&valid), ENTRY_EXPORT),
            Ok(crate::RunValue::Outcome(EntryOutcome::Ok(
                EntrySuccess::Bool(false)
            )))
        );
        assert!(matches!(
            run(&module, ENTRY_EXPORT),
            Err(RunError::Signature(_))
        ));
        let duplicate = with_custom_section(&attach(&valid), SECTION, &valid);
        assert_eq!(
            run(&duplicate, ENTRY_EXPORT),
            Err(invalid("duplicate entry metadata"))
        );

        let mut bad = vec![valid[..9].to_vec(), vec![0; 8192]];
        for (index, value) in [
            (0, 1),
            (0, 3),
            (1, 9),
            (2, 0),
            (3, 3),
            (4, 1),
            (5, 8),
            (9, 0),
            (13, 255),
        ] {
            let mut modified = valid.clone();
            modified[index] = value;
            bad.push(modified);
        }
        for name in ["bad\nname", "\x1b[2J", "bad\u{2028}name"] {
            let mut injected = valid[..13].to_vec();
            injected.extend(name.as_bytes());
            bad.push(injected);
        }
        for metadata in bad {
            assert_eq!(
                run(&attach(&metadata), ENTRY_EXPORT),
                Err(invalid("invalid or unsupported entry metadata"))
            );
        }
    }

    #[test]
    fn decodes_optional_result_entries() {
        let optional = Metadata {
            family: Family::OptionalResult,
            success: Scalar::Bool,
            payload_offset: 4,
            inner_offset: 1,
            size: 12,
            error_id: 1,
            error_name: "pkg::mod::ErrorType",
        }
        .encode()
        .unwrap();
        let run_guest = |result: [u8; 12]| {
            let module = guest(16, 12, result, true);
            run(
                &with_custom_section(&module, SECTION, &optional),
                ENTRY_EXPORT,
            )
        };
        let mut result = [0; 12];
        result[5] = 1;
        assert_eq!(
            run_guest(result),
            Ok(crate::RunValue::Outcome(EntryOutcome::OkSome(
                EntrySuccess::Bool(true)
            )))
        );
        assert_eq!(
            EntryOutcome::OkSome(EntrySuccess::Bool(true)).to_string(),
            "Ok(Some(bool(true)))"
        );
        result[4] = 1;
        assert_eq!(
            run_guest(result),
            Ok(crate::RunValue::Outcome(EntryOutcome::OkNone))
        );
        assert_eq!(EntryOutcome::OkNone.to_string(), "Ok(None)");
        result[4] = 2;
        assert_eq!(run_guest(result), Err(invalid("unknown optional tag")));
        // A `T ! E` metadata block cannot carry an inner offset.
        let mut bad = optional.clone();
        bad[1] = 1;
        let module = guest(16, 12, [0; 12], true);
        assert_eq!(
            run(&with_custom_section(&module, SECTION, &bad), ENTRY_EXPORT),
            Err(invalid("invalid or unsupported entry metadata"))
        );
    }

    #[test]
    fn validates_adapter_signature_and_memory_ranges_and_tags() {
        let valid = metadata();
        let run_guest = |address, size, result, export_memory| {
            let module = guest(address, size, result, export_memory);
            run(&with_custom_section(&module, SECTION, &valid), ENTRY_EXPORT)
        };
        for (address, size) in [
            (0, 12),
            (17, 12),
            (65536, 12),
            (u32::MAX - 15, 12),
            (16, 4),
            (16, u32::MAX),
        ] {
            assert!(matches!(
                run_guest(address, size, [0; 12], true),
                Err(RunError::EntryAbi(_))
            ));
        }
        let mut oversized = valid.clone();
        oversized[5..9].copy_from_slice(&(u32::MAX - 3).to_le_bytes());
        let module = guest(16, u32::MAX - 3, [0; 12], true);
        assert_eq!(
            run(
                &with_custom_section(&module, SECTION, &oversized),
                ENTRY_EXPORT
            ),
            Err(invalid("entry result is outside guest memory"))
        );
        assert_eq!(
            run_guest(16, 12, [0; 12], false),
            Err(invalid("missing 32-bit entry memory export"))
        );

        let mut result = [0; 12];
        result[0] = 3;
        assert_eq!(
            run_guest(16, 12, result, true),
            Err(invalid("unknown entry outcome tag"))
        );
        result[0] = 0;
        result[4] = 2;
        assert_eq!(
            run_guest(16, 12, result, true),
            Err(invalid("invalid bool success payload"))
        );
        result[0] = 1;
        assert_eq!(
            run_guest(16, 12, result, true),
            Err(invalid("unrecognized concrete error identity"))
        );

        let mut module = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([], []);
        let mut functions = FunctionSection::new();
        functions.function(0);
        let mut exports = ExportSection::new();
        exports.export(ENTRY_EXPORT, ExportKind::Func, 0);
        let mut code = CodeSection::new();
        let mut adapter = Function::new([]);
        adapter.instruction(&Instruction::End);
        code.function(&adapter);
        module
            .section(&types)
            .section(&functions)
            .section(&exports)
            .section(&code);
        assert_eq!(
            run(
                &with_custom_section(&module.finish(), SECTION, &valid),
                ENTRY_EXPORT
            ),
            Err(invalid("unexpected entry function signature"))
        );
    }
}
