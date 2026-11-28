//! Bounded canonical adapter for primitive root `Error` application outcomes.
use memobits_entry_abi::{Family, Metadata, Scalar};
use memobits_ir::{ErrorAncestry, Primitive, Program, Type, TypeDefKind};
use wasm_encoder::{
    CodeSection, EntityType, ExportKind, ExportSection, Function, FunctionSection, ImportSection,
    Instruction, MemArg, MemoryType, Module, TypeSection, ValType,
};

pub(super) struct Adapter {
    pub success: wasm_encoder::PrimitiveValType,
    pub optional: bool,
    pub standalone: bool,
    pub module: Vec<u8>,
}

pub(super) fn prepare(
    core: &[u8],
    program: &Program,
    ty: &Type,
) -> Result<Option<Adapter>, String> {
    let Type::Enum(id) = ty else { return Ok(None) };
    let def = &program.types[id.0 as usize];
    let standalone = match def.entry_outcome {
        Some(memobits_ir::EntryOutcome::Option) => true,
        Some(memobits_ir::EntryOutcome::Result) => false,
        None => return Ok(None),
    };
    if !standalone {
        let TypeDefKind::Enum { variants } = &def.kind else {
            return Ok(None);
        };
        let [Type::Struct(error)] = variants[1].payload.as_slice() else {
            return Ok(None);
        };
        let error = &program.types[error.0 as usize];
        let TypeDefKind::Struct { fields } = &error.kind else {
            return Ok(None);
        };
        if error.error_ancestry != Some(ErrorAncestry::Root)
            || fields.len() != 1
            || fields[0].name != "code"
            || fields[0].ty != Type::Primitive(Primitive::U32)
        {
            return Err("component outcomes currently require the exact root Error type".into());
        }
    }
    let data = memobits_runtime::custom_section(core, memobits_entry_abi::SECTION)
        .ok_or("missing outcome metadata")?;
    let meta = Metadata::decode(data).ok_or("invalid outcome metadata")?;
    if standalone != (meta.family == Family::Option) {
        return Err("incompatible component option metadata".into());
    }
    if !standalone && meta.error_name != "Error" {
        return Err("component outcomes currently require the exact root Error type".into());
    }
    let optional = meta.family == Family::OptionalResult;
    let (success, align) = match meta.success {
        Scalar::Bool => (wasm_encoder::PrimitiveValType::Bool, 4),
        Scalar::I8 => (wasm_encoder::PrimitiveValType::S8, 4),
        Scalar::I16 => (wasm_encoder::PrimitiveValType::S16, 4),
        Scalar::I32 => (wasm_encoder::PrimitiveValType::S32, 4),
        Scalar::I64 => (wasm_encoder::PrimitiveValType::S64, 8),
        Scalar::U8 => (wasm_encoder::PrimitiveValType::U8, 4),
        Scalar::U16 => (wasm_encoder::PrimitiveValType::U16, 4),
        Scalar::U32 => (wasm_encoder::PrimitiveValType::U32, 4),
        Scalar::U64 => (wasm_encoder::PrimitiveValType::U64, 8),
        Scalar::F32 => (wasm_encoder::PrimitiveValType::F32, 4),
        Scalar::F64 => (wasm_encoder::PrimitiveValType::F64, 8),
        Scalar::Char => (wasm_encoder::PrimitiveValType::Char, 4),
    };
    let align = if standalone {
        meta.success.width()
    } else {
        align
    };
    if u32::from(meta.payload_offset) != align {
        return Err("incompatible outcome layout for component adapter".into());
    }
    let mut memory = None;
    for item in wasmparser::Parser::new(0).parse_all(core) {
        if let wasmparser::Payload::MemorySection(section) = item.map_err(|e| e.to_string())? {
            for entry in section {
                let m = entry.map_err(|e| e.to_string())?;
                if memory.is_some() || m.memory64 || m.shared {
                    return Err("unsupported outcome memory".into());
                }
                memory = Some(MemoryType {
                    minimum: m.initial,
                    maximum: m.maximum,
                    memory64: m.memory64,
                    shared: m.shared,
                    page_size_log2: m.page_size_log2,
                });
            }
        }
    }
    let memory = memory.ok_or("missing outcome memory")?;
    let mut module = Module::new();
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32, ValType::I32]);
    types.ty().function([], [ValType::I32]);
    let mut imports = ImportSection::new();
    imports.import("inner", "main", EntityType::Function(0));
    imports.import("inner", "memory", EntityType::Memory(memory));
    let mut functions = FunctionSection::new();
    functions.function(1);
    let mut exports = ExportSection::new();
    exports.export("main", ExportKind::Func, 1);
    let mut body = Function::new([(2, ValType::I32)]);
    body.instruction(&Instruction::Call(0));
    body.instruction(&Instruction::LocalSet(1)); // size
    body.instruction(&Instruction::LocalSet(0)); // address
    body.instruction(&Instruction::LocalGet(1));
    body.instruction(&Instruction::I32Const(meta.size as i32));
    body.instruction(&Instruction::I32Ne);
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Unreachable);
    body.instruction(&Instruction::End);
    // Reject unknown variant tags before canonical lifting.
    body.instruction(&Instruction::LocalGet(0));
    body.instruction(&Instruction::I32Load8U(MemArg {
        offset: 0,
        align: 0,
        target: wasm_encoder::MemArgTarget::Memory(0),
        ordering: None,
    }));
    body.instruction(&Instruction::I32Const(1));
    body.instruction(&Instruction::I32GtU);
    body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
    body.instruction(&Instruction::Unreachable);
    body.instruction(&Instruction::End);
    if standalone {
        let tag = MemArg {
            offset: 0,
            align: 0,
            target: wasm_encoder::MemArgTarget::Memory(0),
            ordering: None,
        };
        body.instruction(&Instruction::LocalGet(0));
        body.instruction(&Instruction::LocalGet(0));
        body.instruction(&Instruction::I32Load8U(tag));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Xor);
        body.instruction(&Instruction::I32Store8(tag));
    } else {
        body.instruction(&Instruction::LocalGet(0));
        body.instruction(&Instruction::I32Load8U(MemArg {
            offset: 0,
            align: 0,
            target: wasm_encoder::MemArgTarget::Memory(0),
            ordering: None,
        }));
        body.instruction(&Instruction::I32Const(1));
        body.instruction(&Instruction::I32Eq);
        body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        let payload = u64::from(meta.payload_offset);
        body.instruction(&Instruction::LocalGet(0));
        body.instruction(&Instruction::I32Load(MemArg {
            offset: payload,
            align: 2,
            target: wasm_encoder::MemArgTarget::Memory(0),
            ordering: None,
        }));
        body.instruction(&Instruction::I32Const(meta.error_id as i32));
        body.instruction(&Instruction::I32Ne);
        body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
        body.instruction(&Instruction::Unreachable);
        body.instruction(&Instruction::End);
        // The private layout prefixes Error.code with an internal identity word.
        // Canonical `record { code: u32 }` has only the code word.
        body.instruction(&Instruction::LocalGet(0));
        body.instruction(&Instruction::LocalGet(0));
        body.instruction(&Instruction::I32Load(MemArg {
            offset: payload + 4,
            align: 2,
            target: wasm_encoder::MemArgTarget::Memory(0),
            ordering: None,
        }));
        body.instruction(&Instruction::I32Store(MemArg {
            offset: payload,
            align: 2,
            target: wasm_encoder::MemArgTarget::Memory(0),
            ordering: None,
        }));
        if optional {
            body.instruction(&Instruction::Else);
            // Private option tags are Some=0, None=1, the reverse of canonical
            // option tags. The scalar payload itself is already correctly aligned.
            let option = MemArg {
                offset: payload,
                align: 0,
                target: wasm_encoder::MemArgTarget::Memory(0),
                ordering: None,
            };
            body.instruction(&Instruction::LocalGet(0));
            body.instruction(&Instruction::I32Load8U(option));
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32GtU);
            body.instruction(&Instruction::If(wasm_encoder::BlockType::Empty));
            body.instruction(&Instruction::Unreachable);
            body.instruction(&Instruction::End);
            body.instruction(&Instruction::LocalGet(0));
            body.instruction(&Instruction::LocalGet(0));
            body.instruction(&Instruction::I32Load8U(option));
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32Xor);
            body.instruction(&Instruction::I32Store8(option));
        }
        body.instruction(&Instruction::End);
    }
    body.instruction(&Instruction::LocalGet(0));
    body.instruction(&Instruction::End);
    let mut code = CodeSection::new();
    code.function(&body);
    module
        .section(&types)
        .section(&imports)
        .section(&functions)
        .section(&exports)
        .section(&code);
    Ok(Some(Adapter {
        success,
        optional,
        standalone,
        module: module.finish(),
    }))
}
