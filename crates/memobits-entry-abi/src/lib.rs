//! Private wire format shared by the Wasm backend and runner.

pub const SECTION: &str = "memobits.entry";
pub const ENTRY_EXPORT: &str = "main";
pub const MEMORY_EXPORT: &str = "__mb_entry_memory_v1";
pub const RESULT_ALIGNMENT: u32 = 16;
pub const ERROR_ID_BYTES: u32 = 4;
/// Version 2 replaced the three-state Attempt family with a `T ?! E` family and
/// added the optional payload offset.
const VERSION: u8 = 2;
const HEADER_BYTES: usize = 13;
const MAX_NAME_BYTES: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Family {
    /// `T ! E`: tag 0 is `Ok(T)`, tag 1 is `Err(E)`.
    Result,
    /// `T ?! E` (`Result<Option<T>, E>`): the `Ok` payload is an optional cell
    /// whose tag (0 = `Some`, 1 = `None`) sits at `payload_offset`.
    OptionalResult,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Scalar {
    Bool = 1,
    I8 = 2,
    I16 = 3,
    I32 = 4,
    I64 = 5,
    U8 = 6,
    U16 = 7,
    U32 = 8,
    U64 = 9,
    F32 = 10,
    F64 = 11,
}

impl Scalar {
    fn from_tag(tag: u8) -> Option<Self> {
        Some(match tag {
            1 => Self::Bool,
            2 => Self::I8,
            3 => Self::I16,
            4 => Self::I32,
            5 => Self::I64,
            6 => Self::U8,
            7 => Self::U16,
            8 => Self::U32,
            9 => Self::U64,
            10 => Self::F32,
            11 => Self::F64,
            _ => return None,
        })
    }

    pub fn width(self) -> u32 {
        match self {
            Self::Bool | Self::I8 | Self::U8 => 1,
            Self::I16 | Self::U16 => 2,
            Self::I32 | Self::U32 | Self::F32 => 4,
            Self::I64 | Self::U64 | Self::F64 => 8,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Metadata<'a> {
    pub family: Family,
    pub success: Scalar,
    pub payload_offset: u8,
    /// Offset of the scalar from `payload_offset` for `OptionalResult`; zero for `Result`.
    pub inner_offset: u8,
    pub size: u32,
    pub error_id: u32,
    pub error_name: &'a str,
}

impl<'a> Metadata<'a> {
    pub fn encode(self) -> Option<Vec<u8>> {
        if !self.valid() {
            return None;
        }
        let family = match self.family {
            Family::Result => 1,
            Family::OptionalResult => 2,
        };
        let mut bytes = vec![
            VERSION,
            family,
            self.success as u8,
            self.payload_offset,
            self.inner_offset,
        ];
        bytes.extend(self.size.to_le_bytes());
        bytes.extend(self.error_id.to_le_bytes());
        bytes.extend(self.error_name.as_bytes());
        Some(bytes)
    }

    pub fn decode(bytes: &'a [u8]) -> Option<Self> {
        if !(HEADER_BYTES + 1..=HEADER_BYTES + MAX_NAME_BYTES).contains(&bytes.len()) {
            return None;
        }
        let [VERSION, family, scalar, payload_offset, inner_offset] = bytes[..5] else {
            return None;
        };
        let metadata = Self {
            family: match family {
                1 => Family::Result,
                2 => Family::OptionalResult,
                _ => return None,
            },
            success: Scalar::from_tag(scalar)?,
            payload_offset,
            inner_offset,
            size: u32::from_le_bytes(bytes[5..9].try_into().ok()?),
            error_id: u32::from_le_bytes(bytes[9..13].try_into().ok()?),
            error_name: std::str::from_utf8(&bytes[HEADER_BYTES..]).ok()?,
        };
        metadata.valid().then_some(metadata)
    }

    fn valid(self) -> bool {
        let offset = u32::from(self.payload_offset);
        matches!(offset, 4 | 8)
            && offset >= self.success.width()
            && match self.family {
                Family::Result => self.inner_offset == 0,
                Family::OptionalResult => {
                    u32::from(self.inner_offset) == self.success.width()
                        && self.size >= offset + u32::from(self.inner_offset) + self.success.width()
                }
            }
            && self.size >= offset + ERROR_ID_BYTES + 4
            && self.size.is_multiple_of(offset)
            && self.error_id != 0
            && (1..=MAX_NAME_BYTES).contains(&self.error_name.len())
            && !self
                .error_name
                .chars()
                .any(|ch| ch.is_control() || matches!(ch, '\u{2028}' | '\u{2029}'))
    }
}
