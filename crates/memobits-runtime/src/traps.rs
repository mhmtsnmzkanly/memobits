//! Checked-trap reporting: reason codes, the source location table and its
//! Wasm custom section.
//!
//! Protocol (see `docs/design/wasm-backend.md`): before a checked operation
//! traps, generated code stores `(location_id << 8) | reason_code` into the
//! exported global `__mb_trap` and executes `unreachable`. Native division
//! sites store their code before dividing and let Wasm trap by itself. The
//! location id indexes the `memobits.traps` custom section, a plain-text table
//! mapping ids to source positions, so an artifact is self-describing.

/// Export name of the trap record global (the value of
/// `memobits_wasm::TRAP_EXPORT`; the runtime does not depend on the backend).
pub(crate) const TRAP_EXPORT: &str = "__mb_trap";

/// Name of the custom section holding the location table (the value of
/// `memobits_wasm::TRAP_SECTION`).
pub const TRAP_SECTION: &str = "memobits.traps";

const TABLE_HEADER: &str = "memobits-traps 1";

/// Why a checked operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrapReason {
    AddOverflow,
    SubtractOverflow,
    MultiplyOverflow,
    NegateOverflow,
    DivisionByZero,
    RemainderByZero,
    DivisionOverflow,
    IndexOutOfBounds,
    ArgumentRange,
    HeapAllocation,
    ShiftCount,
    AssertionFailed,
    InvalidFunction,
    MutatingClosure,
}

impl TrapReason {
    /// The reason for an explicit (`unreachable`) trap code; the native
    /// division codes 5 and 6 are not explicit and yield `None`.
    pub fn from_explicit_code(code: u8) -> Option<Self> {
        Some(match code {
            1 => Self::AddOverflow,
            2 => Self::SubtractOverflow,
            3 => Self::MultiplyOverflow,
            4 => Self::NegateOverflow,
            7 => Self::DivisionOverflow,
            8 => Self::IndexOutOfBounds,
            9 => Self::ArgumentRange,
            10 => Self::HeapAllocation,
            11 => Self::ShiftCount,
            12 => Self::AssertionFailed,
            13 => Self::InvalidFunction,
            14 => Self::MutatingClosure,
            _ => return None,
        })
    }

    /// The user-facing description.
    pub fn message(self) -> &'static str {
        match self {
            Self::AddOverflow => "integer overflow in addition",
            Self::SubtractOverflow => "integer overflow in subtraction",
            Self::MultiplyOverflow => "integer overflow in multiplication",
            Self::NegateOverflow => "integer overflow in negation",
            Self::DivisionByZero => "division by zero",
            Self::RemainderByZero => "remainder by zero",
            Self::DivisionOverflow => "integer overflow in division",
            Self::IndexOutOfBounds => "array index out of bounds",
            Self::ArgumentRange => "argument out of range for its parameter type",
            Self::HeapAllocation => "guest heap allocation failed",
            Self::ShiftCount => "shift count must be less than the bit width",
            Self::AssertionFailed => "assertion failed",
            Self::InvalidFunction => "call through an invalid function value",
            Self::MutatingClosure => {
                "a closure that mutates its environment was called through an immutable place; hold it in a `var` or a `share` parameter"
            }
        }
    }
}

/// A resolved source position with the text of its line, so a report needs no
/// access to the source files.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLocation {
    pub file: String,
    /// 1-based.
    pub line: u32,
    /// 1-based, counting Unicode scalars.
    pub column: u32,
    /// Caret width in scalars (at least 1).
    pub width: u32,
    /// The source line without its terminator.
    pub text: String,
}

/// Location ids (1-based, in order) to source positions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TrapTable {
    pub locations: Vec<SourceLocation>,
}

impl TrapTable {
    /// The custom section payload.
    pub fn encode(&self) -> Vec<u8> {
        let mut text = format!("{TABLE_HEADER}\n");
        for location in &self.locations {
            let clean = |value: &str| value.replace(['\t', '\n', '\r'], " ");
            text.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\n",
                clean(&location.file),
                location.line,
                location.column,
                location.width,
                clean(&location.text),
            ));
        }
        text.into_bytes()
    }

    /// Parse a payload; `None` when it is not a table of this format.
    pub fn decode(payload: &[u8]) -> Option<Self> {
        let text = std::str::from_utf8(payload).ok()?;
        let mut lines = text.lines();
        if lines.next()? != TABLE_HEADER {
            return None;
        }
        let mut locations = Vec::new();
        for line in lines {
            let mut fields = line.splitn(5, '\t');
            let location = (|| {
                Some(SourceLocation {
                    file: fields.next()?.to_owned(),
                    line: fields.next()?.parse().ok()?,
                    column: fields.next()?.parse().ok()?,
                    width: fields.next()?.parse().ok()?,
                    text: fields.next()?.to_owned(),
                })
            })();
            // Keep ids aligned even when one record is unreadable.
            locations.push(location.unwrap_or_else(|| SourceLocation {
                file: String::new(),
                line: 0,
                column: 0,
                width: 1,
                text: String::new(),
            }));
        }
        Some(Self { locations })
    }

    /// The location for a 1-based id; unreadable (blank) records are `None`.
    pub fn get(&self, id: u32) -> Option<&SourceLocation> {
        let index = usize::try_from(id).ok()?.checked_sub(1)?;
        self.locations
            .get(index)
            .filter(|location| location.line != 0)
    }
}

/// Append a custom section to a Wasm module.
pub fn with_custom_section(module: &[u8], name: &str, payload: &[u8]) -> Vec<u8> {
    let mut body = Vec::new();
    write_leb(&mut body, name.len() as u32);
    body.extend_from_slice(name.as_bytes());
    body.extend_from_slice(payload);
    let mut out = module.to_vec();
    out.push(0);
    write_leb(&mut out, body.len() as u32);
    out.extend_from_slice(&body);
    out
}

/// Append `table` to a module as the `memobits.traps` section.
pub fn with_trap_table(module: &[u8], table: &TrapTable) -> Vec<u8> {
    with_custom_section(module, TRAP_SECTION, &table.encode())
}

/// The payload of the first custom section called `name`, if the module's
/// section framing is readable up to it.
pub fn custom_section<'a>(module: &'a [u8], name: &str) -> Option<&'a [u8]> {
    custom_sections(module, name).next()
}

/// Scan matching sections without copying arbitrary section contents.
pub(crate) fn custom_sections<'a, 'n>(
    module: &'a [u8],
    name: &'n str,
) -> impl Iterator<Item = &'a [u8]> + 'n
where
    'a: 'n,
{
    let mut rest = module.get(8..).unwrap_or_default();
    std::iter::from_fn(move || {
        while let Some((&id, tail)) = rest.split_first() {
            let (size, tail) = read_leb(tail)?;
            let (payload, remaining) = tail.split_at_checked(size as usize)?;
            rest = remaining;
            if id == 0 {
                let (name_len, after) = read_leb(payload)?;
                let (section_name, data) = after.split_at_checked(name_len as usize)?;
                if section_name == name.as_bytes() {
                    return Some(data);
                }
            }
        }
        None
    })
}

fn write_leb(out: &mut Vec<u8>, mut value: u32) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn read_leb(bytes: &[u8]) -> Option<(u32, &[u8])> {
    let mut value = 0u32;
    for (index, &byte) in bytes.iter().enumerate().take(5) {
        if index == 4 && byte > 0x0f {
            return None;
        }
        value |= u32::from(byte & 0x7f) << (7 * index);
        if byte & 0x80 == 0 {
            return Some((value, &bytes[index + 1..]));
        }
    }
    None
}
