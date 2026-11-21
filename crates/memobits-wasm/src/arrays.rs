//! Inline array-cell lookup and copying for function frames.
use super::{
    emit_address, emit_operand, ArrayCell, FrameLayout, FrameState, Function, Operand, Slot, Source,
};
use wasm_encoder::{Function as WasmFunction, Instruction};

pub(super) fn array_cell(layout: &FrameLayout, operand: &Operand) -> Option<ArrayCell> {
    let slot = match operand.source {
        Source::Local(local) => Slot::Local(local.0),
        Source::Value(value) => Slot::Value(value.0),
        Source::Function(_) => return None,
    };
    layout.arrays.get(&slot).copied()
}

pub(super) fn array_cell_of(layout: &FrameLayout, slot: Slot) -> Result<ArrayCell, String> {
    layout
        .arrays
        .get(&slot)
        .copied()
        .ok_or_else(|| "array storage cell is missing".to_string())
}

/// Copy a whole array between two cells of identical layout.
pub(super) fn emit_array_copy(
    body: &mut WasmFunction,
    function: &Function,
    param_count: u32,
    destination: ArrayCell,
    source: &Operand,
    layout: &FrameLayout,
    frame: Option<FrameState>,
) -> Result<(), String> {
    let frame = frame.ok_or("array cell requires frame")?;
    if array_cell(layout, source).is_some_and(|cell| cell.offset == destination.offset) {
        return Ok(());
    }
    emit_address(body, frame, destination.offset);
    emit_operand(body, function, param_count, source, layout, frame.into())?;
    body.instruction(&Instruction::I32Const(destination.size as i32));
    body.instruction(&Instruction::MemoryCopy {
        src_mem: 0,
        dst_mem: 0,
    });
    Ok(())
}
