//! Checked placement of fixed regions in guest Wasm32 memory.

use super::static_data_start;

const PAGE_BYTES: u64 = 65_536;
// Keep the existing backend limit, below a full 4 GiB memory.
const MAX_PAGES: u64 = 65_535;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LayoutError {
    AddressOverflow,
    PageLimit,
}

/// The exclusive end of the stack and any appended static regions.
#[derive(Clone, Copy, Debug)]
pub(super) struct StaticLayout {
    end: u32,
}

impl StaticLayout {
    pub(super) fn new(stack_size: u32) -> Option<Self> {
        if stack_size == 0 || !stack_size.is_multiple_of(16) {
            return None;
        }
        let layout = Self {
            end: static_data_start(stack_size)?,
        };
        (layout.pages() <= MAX_PAGES).then_some(layout)
    }

    /// Append a packed region and return its start. A failure leaves the
    /// layout at its previous end.
    pub(super) fn reserve(&mut self, bytes: u32) -> Result<u32, LayoutError> {
        let end = self
            .end
            .checked_add(bytes)
            .ok_or(LayoutError::AddressOverflow)?;
        let next = Self { end };
        if next.pages() > MAX_PAGES {
            return Err(LayoutError::PageLimit);
        }
        let start = self.end;
        *self = next;
        Ok(start)
    }

    pub(super) fn pages(self) -> u64 {
        u64::from(self.end).div_ceil(PAGE_BYTES)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aligned_stack_and_packed_static_regions_round_only_at_the_memory_end() {
        let mut layout = StaticLayout::new(65_504).unwrap();
        assert_eq!(layout.reserve(12), Ok(65_520));
        assert_eq!(layout.pages(), 1);
        assert_eq!(layout.reserve(4), Ok(65_532));
        assert_eq!(layout.pages(), 1);
        assert_eq!(layout.reserve(1), Ok(65_536));
        assert_eq!(layout.pages(), 2);
        assert!(StaticLayout::new(65_505).is_none());
    }

    #[test]
    fn failed_reservations_leave_the_cursor_available_for_retry() {
        let limit = (MAX_PAGES * PAGE_BYTES) as u32;
        let mut layout = StaticLayout::new(limit - 32).unwrap();
        let end = limit - 16;
        assert_eq!(layout.reserve(17), Err(LayoutError::PageLimit));
        assert_eq!(layout.reserve(u32::MAX), Err(LayoutError::AddressOverflow));
        assert_eq!(layout.reserve(16), Ok(end));
        assert_eq!(layout.pages(), MAX_PAGES);
        assert!(StaticLayout::new(limit).is_none());
        assert!(StaticLayout::new(u32::MAX - 15).is_none());
    }
}
