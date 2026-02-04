//! Koleksiyon tipleri (std/no_std uyumlu).

#[cfg(feature = "std")]
pub use std::collections::{HashMap, HashSet};

#[cfg(not(feature = "std"))]
pub use alloc::collections::{BTreeMap as HashMap, BTreeSet as HashSet};
