//! Natural-alignment aggregate layout for structs, enums and arrays.
use super::*;

/// How one struct field is stored: a primitive written with a typed store, or a
/// nested array or struct copied as `size` bytes from its value cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FieldStorage {
    Primitive(Primitive),
    Aggregate(u32),
}

/// Natural-alignment layout of a struct or enum. A struct lays its fields out
/// in declaration order, each at the next offset aligned to its own alignment,
/// total size rounded up to the largest field alignment. An enum (`variants` is
/// `Some`) stores its tag at offset 0 and every variant's payload in one shared
/// area; `offsets` and `fields` are empty for it. A nested aggregate is laid
/// out inline with its own size and alignment (the validator rejects by-value
/// cycles).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct StructLayout {
    pub(super) size: u32,
    pub(super) align: u32,
    pub(super) offsets: Vec<u32>,
    pub(super) fields: Vec<FieldStorage>,
    pub(super) enum_layout: Option<EnumLayout>,
    pub(super) error_identity: Option<u32>,
    pub(super) has_string_fields: bool,
    pub(super) is_tuple: bool,
    /// Flat nominal String-owning struct admitted by the shared transport predicate.
    pub(super) is_flat_string_owner: bool,
}

impl StructLayout {
    pub(super) fn has_string_fields(&self) -> bool {
        self.has_string_fields
    }
}

/// Enum layout: the tag at offset 0 with the smallest unsigned width that holds
/// the variant count (1 byte up to 256 variants, 2 up to 65536, else 4), then
/// the payload area, aligned to the largest payload alignment of any variant.
/// Each variant places its payload fields from the start of that area, so the
/// size is the largest variant extent, rounded up to the enum's alignment. The
/// layout is internal, not a stable ABI, and bytes beyond the active variant's
/// payload are unspecified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct EnumLayout {
    pub(super) tag_size: u32,
    pub(super) variants: Vec<VariantLayout>,
    pub(super) string_variants: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct VariantLayout {
    pub(super) offsets: Vec<u32>,
    pub(super) fields: Vec<FieldStorage>,
}

pub(super) const STRUCT_LAYOUT_OVERFLOW: &str = "struct layout overflows the 32-bit address space";
pub(super) fn type_has_string_storage(types: &[TypeDef], ty: &Type) -> bool {
    pub(super) fn has(types: &[TypeDef], ty: &Type, visited: &mut HashSet<u32>) -> bool {
        match ty {
            Type::String | Type::List(_) => true,
            Type::Array { element, len } => *len != 0 && has(types, element, visited),
            Type::Struct(id) | Type::Enum(id) => {
                if !visited.insert(id.0) {
                    return false;
                }
                let result = match types.get(id.0 as usize).map(|definition| &definition.kind) {
                    Some(TypeDefKind::Struct { fields }) => {
                        fields.iter().any(|field| has(types, &field.ty, visited))
                    }
                    Some(TypeDefKind::Enum { variants }) => variants
                        .iter()
                        .flat_map(|variant| &variant.payload)
                        .any(|field| has(types, field, visited)),
                    None => false,
                };
                visited.remove(&id.0);
                result
            }
            _ => false,
        }
    }
    has(types, ty, &mut HashSet::new())
}

pub(super) fn struct_layouts(types: &[TypeDef]) -> Result<Vec<StructLayout>, String> {
    let mut done: Vec<Option<StructLayout>> = vec![None; types.len()];
    for index in 0..types.len() {
        struct_layout_at(types, index, &mut done, &mut Vec::new())?;
    }
    Ok(done
        .into_iter()
        .map(|layout| layout.expect("laid out"))
        .collect())
}

/// Size, alignment and storage kind of one field or payload value.
pub(super) fn member_layout(
    types: &[TypeDef],
    ty: &Type,
    done: &mut Vec<Option<StructLayout>>,
    active: &mut Vec<usize>,
    allow_nested_string_tuple: bool,
    allow_flat_string_owner: bool,
) -> Result<Option<(u32, u32, FieldStorage)>, String> {
    Ok(match ty {
        Type::Primitive(kind) => {
            let (size, align) = storage_layout(*kind)?;
            Some((size, align, FieldStorage::Primitive(*kind)))
        }
        Type::Reference { inner, .. } if **inner == Type::String => {
            return Err("Wasm does not yet support String fields or enum payloads".into());
        }
        // Validated local borrow Option payloads store a Wasm address.
        Type::Reference { .. } => Some((4, 4, FieldStorage::Primitive(Primitive::U32))),
        Type::String => {
            return Err("Wasm does not yet support String fields or enum payloads".into())
        }
        nested @ (Type::Array { .. } | Type::Struct(_) | Type::Enum(_)) => {
            nested_struct_layouts(types, nested, done, active)?;
            let layout_at = |id: u32| done.get(id as usize).and_then(Option::as_ref);
            if matches!(nested, Type::Struct(id) if layout_at(id.0).is_some_and(|layout| layout.has_string_fields())
                && !(allow_nested_string_tuple && is_tuple_definition(types, id.0))
                && !(allow_flat_string_owner
                    && memobits_ir::is_string_owner_transport(types, nested)))
            {
                return Err("Wasm does not yet support nesting structs with String fields".into());
            }
            let (size, align) = type_layout(&layout_at, nested)?;
            Some((size, align, FieldStorage::Aggregate(size)))
        }
        _ => None,
    })
}

pub(super) fn is_tuple_definition(types: &[TypeDef], id: u32) -> bool {
    types.get(id as usize).is_some_and(|definition| {
        definition.path.module.as_slice() == ["\0tuple"]
            && matches!(&definition.kind, TypeDefKind::Struct { .. })
    })
}

pub(super) fn struct_layout_at(
    types: &[TypeDef],
    index: usize,
    done: &mut Vec<Option<StructLayout>>,
    active: &mut Vec<usize>,
) -> Result<(), String> {
    if done[index].is_some() {
        return Ok(());
    }
    let definition = &types[index];
    if active.contains(&index) {
        let what = match definition.kind {
            TypeDefKind::Struct { .. } => "struct",
            TypeDefKind::Enum { .. } => "enum",
        };
        return Err(format!(
            "{what} '{}' contains itself by value",
            definition.path.name
        ));
    }
    active.push(index);
    let layout = match &definition.kind {
        TypeDefKind::Struct { fields } => {
            let has_string_fields = fields
                .iter()
                .any(|field| matches!(field.ty, Type::String | Type::List(_)));
            let is_tuple = definition.path.module.as_slice() == ["\0tuple"];
            if definition.error_ancestry.is_some()
                && fields
                    .iter()
                    .any(|field| type_has_string_storage(types, &field.ty))
            {
                return Err(format!(
                    "Error-derived type '{}' cannot own heap Strings yet: a field holds a String directly or through a nested struct, array or enum",
                    definition.path.name
                ));
            }
            if has_string_fields
                && (definition.error_ancestry.is_some()
                    || (!is_tuple
                        && !memobits_ir::is_string_owner_transport(
                            types,
                            &Type::Struct(memobits_ir::TypeId(index as u32)),
                        )))
            {
                return Err("structs with String fields support only String and primitive fields and cannot inherit from Error".into());
            }
            let mut offset = if definition.error_ancestry == Some(ErrorAncestry::Root) {
                entry_abi::ERROR_ID_BYTES
            } else {
                0
            };
            let mut align = 1u32;
            let mut offsets = Vec::with_capacity(fields.len());
            let mut storage = Vec::with_capacity(fields.len());
            if let Some(ErrorAncestry::Derived(parent)) = definition.error_ancestry {
                let parent = parent.0 as usize;
                struct_layout_at(types, parent, done, active)?;
                let base = done[parent].as_ref().expect("laid out parent");
                // Whole stores through a Share of the ancestor copy its padded size.
                // Reserve that entire prefix before placing any descendant fields.
                offset = base.size;
                align = base.align;
                offsets.extend_from_slice(&base.offsets);
                storage.extend_from_slice(&base.fields);
            }
            for field in &fields[offsets.len()..] {
                let member = if field.ty == Type::String {
                    Some((
                        string_descriptor::SIZE,
                        string_descriptor::ALIGN,
                        FieldStorage::Aggregate(string_descriptor::SIZE),
                    ))
                } else if matches!(field.ty, Type::List(_)) {
                    Some((
                        list_descriptor::SIZE,
                        list_descriptor::ALIGN,
                        FieldStorage::Aggregate(list_descriptor::SIZE),
                    ))
                } else {
                    member_layout(
                        types,
                        &field.ty,
                        done,
                        active,
                        true,
                        is_tuple
                            || memobits_ir::is_string_owner_transport(
                                types,
                                &Type::Struct(memobits_ir::TypeId(index as u32)),
                            ),
                    )?
                };
                let Some((size, field_align, kind)) = member else {
                    return Err(format!(
                        "field '{}' of struct '{}' has an unsupported type",
                        field.name, definition.path.name
                    ));
                };
                offset = align_up(offset, field_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                offsets.push(offset);
                storage.push(kind);
                offset = offset.checked_add(size).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                align = align.max(field_align);
            }
            StructLayout {
                size: align_up(offset, align).ok_or(STRUCT_LAYOUT_OVERFLOW)?,
                align,
                has_string_fields: fields
                    .iter()
                    .any(|field| type_has_string_storage(types, &field.ty)),
                offsets,
                fields: storage,
                enum_layout: None,
                error_identity: definition.error_ancestry.map(|_| index as u32 + 1),
                is_tuple,
                is_flat_string_owner: !is_tuple
                    && memobits_ir::is_string_owner_transport(
                        types,
                        &Type::Struct(memobits_ir::TypeId(index as u32)),
                    ),
            }
        }
        TypeDefKind::Enum { variants } => {
            let tag_size = match variants.len() {
                0..=256 => 1u32,
                257..=65536 => 2,
                _ => 4,
            };
            // First pass: member sizes, so the payload area's alignment is known.
            let mut sized: Vec<Vec<(u32, u32, FieldStorage)>> = Vec::with_capacity(variants.len());
            let mut payload_align = 1u32;
            for variant in variants {
                let mut members = Vec::with_capacity(variant.payload.len());
                for ty in &variant.payload {
                    let member = if *ty == Type::String {
                        Some((
                            string_descriptor::SIZE,
                            string_descriptor::ALIGN,
                            FieldStorage::Aggregate(string_descriptor::SIZE),
                        ))
                    } else if matches!(ty, Type::List(_)) {
                        // A List payload is the List descriptor.
                        Some((
                            list_descriptor::SIZE,
                            list_descriptor::ALIGN,
                            FieldStorage::Aggregate(list_descriptor::SIZE),
                        ))
                    } else {
                        member_layout(types, ty, done, active, true, true)?
                    };
                    let Some(member) = member else {
                        return Err(format!(
                            "payload of variant '{}' of enum '{}' has an unsupported type",
                            variant.name, definition.path.name
                        ));
                    };
                    payload_align = payload_align.max(member.1);
                    members.push(member);
                }
                sized.push(members);
            }
            let payload_start = align_up(tag_size, payload_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
            let align = payload_align.max(tag_size);
            let mut extent = tag_size;
            let mut laid_out = Vec::with_capacity(sized.len());
            let mut string_variants = Vec::with_capacity(sized.len());
            for members in sized {
                let mut cursor = payload_start;
                let mut offsets = Vec::with_capacity(members.len());
                let mut fields = Vec::with_capacity(members.len());
                for (size, member_align, kind) in members {
                    cursor = align_up(cursor, member_align).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                    offsets.push(cursor);
                    fields.push(kind);
                    cursor = cursor.checked_add(size).ok_or(STRUCT_LAYOUT_OVERFLOW)?;
                }
                let variant_index = laid_out.len();
                string_variants.push(
                    variants[variant_index]
                        .payload
                        .iter()
                        .any(|field| type_has_string_storage(types, field)),
                );
                extent = extent.max(cursor);
                laid_out.push(VariantLayout { offsets, fields });
            }
            StructLayout {
                size: align_up(extent, align).ok_or(STRUCT_LAYOUT_OVERFLOW)?,
                align,
                offsets: Vec::new(),
                fields: Vec::new(),
                error_identity: None,
                has_string_fields: string_variants.iter().any(|owns| *owns),
                is_tuple: false,
                is_flat_string_owner: false,
                enum_layout: Some(EnumLayout {
                    tag_size,
                    variants: laid_out,
                    string_variants,
                }),
            }
        }
    };
    done[index] = Some(layout);
    active.pop();
    Ok(())
}

/// Lay out every struct or enum reachable from a field type before the field itself.
pub(super) fn nested_struct_layouts(
    types: &[TypeDef],
    ty: &Type,
    done: &mut Vec<Option<StructLayout>>,
    active: &mut Vec<usize>,
) -> Result<(), String> {
    match ty {
        Type::Struct(id) | Type::Enum(id) => struct_layout_at(types, id.0 as usize, done, active),
        Type::Array { element, .. } => nested_struct_layouts(types, element, done, active),
        _ => Ok(()),
    }
}

/// Size and alignment of an array or struct type. Arrays multiply the element
/// size by the length with checked arithmetic at every level; the cost depends
/// on the nesting depth of the type only, never on a source-supplied count.
pub(super) fn aggregate_layout(structs: &[StructLayout], ty: &Type) -> Result<(u32, u32), String> {
    type_layout(&|id| structs.get(id as usize), ty)
}

pub(super) fn type_layout<'a>(
    struct_layout: &dyn Fn(u32) -> Option<&'a StructLayout>,
    ty: &Type,
) -> Result<(u32, u32), String> {
    match ty {
        Type::Primitive(kind) => storage_layout(*kind),
        Type::String => Ok((string_descriptor::SIZE, string_descriptor::ALIGN)),
        Type::List(_) => Ok((list_descriptor::SIZE, list_descriptor::ALIGN)),
        Type::Struct(id) | Type::Enum(id) => struct_layout(id.0)
            .map(|layout| (layout.size, layout.align))
            .ok_or_else(|| "type is out of range".to_string()),
        Type::Array { element, len } => {
            if matches!(element.as_ref(), Type::Struct(id)
                if struct_layout(id.0).is_some_and(|layout|
                    layout.has_string_fields()
                        && !layout.is_tuple
                        && !layout.is_flat_string_owner))
            {
                return Err("Wasm does not yet support nesting structs with String fields".into());
            }
            let (size, align) = type_layout(struct_layout, element)?;
            let bytes = len.checked_mul(size).ok_or(LAYOUT_OVERFLOW)?;
            Ok((bytes, align))
        }
        _ => Err(
            "array elements must be primitives, structs, enums or arrays in frame layout".into(),
        ),
    }
}
