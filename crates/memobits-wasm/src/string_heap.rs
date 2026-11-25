//! Private whole-block allocator shared by String and List.

use super::{memory, memory_arg, string_descriptor, Primitive};
use wasm_encoder::{BlockType, Function, Instruction as I, MemArg, ValType};

pub(super) const CURSOR_GLOBAL: u32 = 3;
pub(super) const FREE_GLOBAL: u32 = 4;
pub(super) const BLOCK_ALIGN: u32 = 4;
const CAPACITY_OFFSET: u64 = 0;
pub(super) const NEXT_OFFSET: u64 = 4;
pub(super) const HEADER_BYTES: i32 = 8;

const LEN: u32 = 0;
const BLOCK: u32 = 1;
const PREVIOUS: u32 = 2;
const PAGES: u32 = 3;
const END: u32 = 4;

/// Largest capacity served from the size-class table. Larger blocks live on
/// one exact-size list (`FREE_GLOBAL`) searched first-fit.
const CLASS_LIMIT: i32 = 1 << 16;
/// Classes: 8 four-byte steps up to 32 bytes, then four classes per octave.
const CLASS_COUNT: u32 = 52;
/// Static table: a 64-bit non-empty-class bitmap, then one head per class.
pub(super) const TABLE_BYTES: u32 = 8 + 4 * CLASS_COUNT;
const HEADS_OFFSET: i32 = 8;

const SIZE: u32 = 5;
const CLASS: u32 = 6;
const SHIFT: u32 = 7;

/// Round the byte count in `len_local` (at most [`CLASS_LIMIT`]) up to its
/// class size, stored in `size`, and store the class index in `class`.
fn emit_class(body: &mut Function, len_local: u32, size: u32, class: u32, shift: u32) {
    body.instructions()
        .local_get(len_local)
        .i32_const(3)
        .i32_add()
        .i32_const(-4)
        .i32_and()
        .local_tee(size)
        .i32_eqz()
        .if_(BlockType::Empty)
        .i32_const(4)
        .local_set(size)
        .end();
    body.instructions()
        .local_get(size)
        .i32_const(32)
        .i32_le_u()
        .if_(BlockType::Empty)
        .local_get(size)
        .i32_const(2)
        .i32_shr_u()
        .i32_const(1)
        .i32_sub()
        .local_set(class)
        .else_()
        // shift = floor(log2(size - 1)) - 2: four classes per octave.
        .i32_const(29)
        .local_get(size)
        .i32_const(1)
        .i32_sub()
        .i32_clz()
        .i32_sub()
        .local_set(shift)
        .local_get(size)
        .i32_const(1)
        .i32_sub()
        .local_get(shift)
        .i32_shr_u()
        .local_set(class)
        .local_get(class)
        .i32_const(1)
        .i32_add()
        .local_get(shift)
        .i32_shl()
        .local_set(size)
        .i32_const(8)
        .local_get(shift)
        .i32_const(3)
        .i32_sub()
        .i32_const(2)
        .i32_shl()
        .i32_add()
        .local_get(class)
        .i32_const(3)
        .i32_and()
        .i32_add()
        .local_set(class)
        .end();
}

fn bitmap_arg() -> MemArg {
    MemArg {
        offset: 0,
        align: 2,
        target: wasm_encoder::MemArgTarget::Memory(0),
        ordering: None,
    }
}

/// Reserve a whole block by byte capacity. Return zero on failure without
/// changing the heap cursor or free lists. Small requests round up to a size
/// class and pop the smallest non-empty class that fits; large requests search
/// the exact-size list first-fit.
pub(super) fn reserve(table: u32) -> Function {
    // Locals: 0 len, 1 block, 2 previous, 3 pages, 4 end (i64), 5 size,
    // 6 class, 7 shift (reused as the class-head slot address).
    let mut body = Function::new([(3, ValType::I32), (1, ValType::I64), (3, ValType::I32)]);
    body.instructions()
        .local_get(LEN)
        .i32_const(CLASS_LIMIT)
        .i32_gt_u()
        .if_(BlockType::Empty);
    // Large: search without changing the list. Every linked block came from
    // this allocator and has an aligned header in already committed memory.
    body.instructions()
        .global_get(FREE_GLOBAL)
        .local_set(BLOCK)
        .block(BlockType::Empty)
        .loop_(BlockType::Empty)
        .local_get(BLOCK)
        .i32_eqz()
        .br_if(1)
        .local_get(BLOCK)
        .i32_load(header_field(CAPACITY_OFFSET))
        .local_get(LEN)
        .i32_ge_u()
        .br_if(1)
        .local_get(BLOCK)
        .local_tee(PREVIOUS)
        .i32_load(header_field(NEXT_OFFSET))
        .local_set(BLOCK)
        .br(0)
        .end()
        .end();
    body.instructions()
        .local_get(BLOCK)
        .i32_eqz()
        .if_(BlockType::Empty);
    extend_heap(&mut body);
    body.instruction(&I::Else);
    unlink_block(&mut body);
    body.instruction(&I::End);
    body.instruction(&I::Else);

    // Small: first non-empty class at or above the request's class.
    emit_class(&mut body, LEN, SIZE, CLASS, SHIFT);
    body.instructions()
        .i32_const(table as i32)
        .i64_load(bitmap_arg())
        .i64_const(-1)
        .local_get(CLASS)
        .i64_extend_i32_u()
        .i64_shl()
        .i64_and()
        .local_tee(END)
        .i64_eqz()
        .if_(BlockType::Empty)
        // No small block fits: reuse the head of the large list, else grow.
        .global_get(FREE_GLOBAL)
        .local_tee(BLOCK)
        .if_(BlockType::Empty)
        .local_get(BLOCK)
        .i32_load(header_field(NEXT_OFFSET))
        .global_set(FREE_GLOBAL)
        .else_()
        .local_get(SIZE)
        .local_set(LEN);
    extend_heap(&mut body);
    body.instructions()
        .end()
        .else_()
        // The lowest set bit of the mask is the class to pop.
        .local_get(END)
        .i64_ctz()
        .i32_wrap_i64()
        .local_tee(CLASS)
        .i32_const(2)
        .i32_shl()
        .i32_const(table as i32 + HEADS_OFFSET)
        .i32_add()
        .local_tee(SHIFT)
        .i32_load(header_field(0))
        .local_tee(BLOCK)
        .i32_load(header_field(NEXT_OFFSET))
        .local_set(PREVIOUS)
        .local_get(SHIFT)
        .local_get(PREVIOUS)
        .i32_store(header_field(0))
        .local_get(PREVIOUS)
        .i32_eqz()
        .if_(BlockType::Empty)
        // The class became empty: clear its bitmap bit.
        .i32_const(table as i32)
        .i32_const(table as i32)
        .i64_load(bitmap_arg())
        .i64_const(1)
        .local_get(CLASS)
        .i64_extend_i32_u()
        .i64_shl()
        .i64_const(-1)
        .i64_xor()
        .i64_and()
        .i64_store(bitmap_arg())
        .end()
        .end()
        .end();

    body.instructions().local_get(BLOCK).end();
    body
}

/// Allocate and copy two already validated UTF-8 ranges.
pub(super) fn copy_ranges(reserve: u32) -> Function {
    const LEFT: u32 = 0;
    const LEFT_LEN: u32 = 1;
    const RIGHT: u32 = 2;
    const RIGHT_LEN: u32 = 3;
    const DESTINATION: u32 = 4;
    const LEN: u32 = 5;
    const BLOCK: u32 = 6;
    const END: u32 = 7;
    let mut body = Function::new([(2, ValType::I32), (1, ValType::I64)]);
    body.instructions()
        .local_get(LEFT_LEN)
        .i64_extend_i32_u()
        .local_get(RIGHT_LEN)
        .i64_extend_i32_u()
        .i64_add()
        .local_tee(END)
        .i64_const((memory::MAX_PAGES * memory::PAGE_BYTES) as i64)
        .i64_gt_u();
    failure_if(&mut body);
    body.instructions()
        .local_get(END)
        .i32_wrap_i64()
        .local_tee(LEN)
        .call(reserve)
        .local_tee(BLOCK)
        .i32_eqz();
    failure_if(&mut body);

    for (address, length) in [(LEFT, LEFT_LEN), (RIGHT, RIGHT_LEN)] {
        body.instructions()
            .local_get(BLOCK)
            .i32_const(HEADER_BYTES)
            .i32_add();
        if address == RIGHT {
            body.instructions().local_get(LEFT_LEN).i32_add();
        }
        body.instructions()
            .local_get(address)
            .local_get(length)
            .memory_copy(0, 0);
    }

    body.instructions()
        .local_get(DESTINATION)
        .local_get(BLOCK)
        .i32_const(HEADER_BYTES)
        .i32_add();
    string_descriptor::store_address(&mut body);
    body.instructions().local_get(DESTINATION).local_get(LEN);
    string_descriptor::store_length(&mut body);
    body.instructions().local_get(DESTINATION).local_get(BLOCK);
    string_descriptor::store_allocation(&mut body);
    body.instructions().i32_const(1).end();
    body
}

fn extend_heap(body: &mut Function) {
    // Calculate the aligned exclusive end in i64, including the block header.
    body.instructions()
        .global_get(CURSOR_GLOBAL)
        .local_tee(BLOCK)
        .i64_extend_i32_u()
        .i64_const(i64::from(HEADER_BYTES))
        .i64_add()
        .local_get(LEN)
        .i64_extend_i32_u()
        .i64_add()
        .i64_const(i64::from(BLOCK_ALIGN - 1))
        .i64_add()
        .i64_const(-i64::from(BLOCK_ALIGN))
        .i64_and()
        .local_tee(END)
        .i64_const((memory::MAX_PAGES * memory::PAGE_BYTES) as i64)
        .i64_gt_u();
    failure_if(body);

    body.instructions()
        .local_get(END)
        .i64_const((memory::PAGE_BYTES - 1) as i64)
        .i64_add()
        .i64_const(16)
        .i64_shr_u()
        .i32_wrap_i64()
        .local_tee(PAGES)
        .memory_size(0)
        .i32_gt_u()
        .if_(BlockType::Empty)
        .local_get(PAGES)
        .memory_size(0)
        .i32_sub()
        .memory_grow(0)
        .i32_const(-1)
        .i32_eq();
    failure_if(body);
    body.instruction(&I::End);

    // Only publish the new extent after all checks, including memory.grow.
    body.instructions()
        .local_get(BLOCK)
        .local_get(END)
        .i32_wrap_i64()
        .local_get(BLOCK)
        .i32_sub()
        .i32_const(HEADER_BYTES)
        .i32_sub()
        .i32_store(header_field(CAPACITY_OFFSET))
        .local_get(END)
        .i32_wrap_i64()
        .global_set(CURSOR_GLOBAL);
}

fn unlink_block(body: &mut Function) {
    body.instructions()
        .local_get(PREVIOUS)
        .i32_eqz()
        .if_(BlockType::Empty)
        .local_get(BLOCK)
        .i32_load(header_field(NEXT_OFFSET))
        .global_set(FREE_GLOBAL)
        .else_()
        .local_get(PREVIOUS)
        .local_get(BLOCK)
        .i32_load(header_field(NEXT_OFFSET))
        .i32_store(header_field(NEXT_OFFSET))
        .end();
}

fn failure_if(body: &mut Function) {
    body.instructions()
        .if_(BlockType::Empty)
        .i32_const(0)
        .return_()
        .end();
}

/// Return a block to its size class (or the large list). Zero denotes an
/// empty or static owner.
pub(super) fn releaser(table: u32) -> Function {
    // Locals: 0 block, 1 capacity, 2 size, 3 class, 4 shift, 5 slot.
    let mut body = Function::new([(5, ValType::I32)]);
    body.instructions()
        .local_get(0)
        .if_(BlockType::Empty)
        .local_get(0)
        .i32_load(header_field(CAPACITY_OFFSET))
        .local_tee(1)
        .i32_const(CLASS_LIMIT)
        .i32_gt_u()
        .if_(BlockType::Empty)
        .local_get(0)
        .global_get(FREE_GLOBAL)
        .i32_store(header_field(NEXT_OFFSET))
        .local_get(0)
        .global_set(FREE_GLOBAL)
        .else_();
    // A small block's capacity is always an exact class size.
    emit_class(&mut body, 1, 2, 3, 4);
    body.instructions()
        .local_get(3)
        .i32_const(2)
        .i32_shl()
        .i32_const(table as i32 + HEADS_OFFSET)
        .i32_add()
        .local_set(5)
        .local_get(0)
        .local_get(5)
        .i32_load(header_field(0))
        .i32_store(header_field(NEXT_OFFSET))
        .local_get(5)
        .local_get(0)
        .i32_store(header_field(0))
        .i32_const(table as i32)
        .i32_const(table as i32)
        .i64_load(bitmap_arg())
        .i64_const(1)
        .local_get(3)
        .i64_extend_i32_u()
        .i64_shl()
        .i64_or()
        .i64_store(bitmap_arg())
        .end()
        .end()
        .end();
    body
}

pub(super) fn load_capacity(body: &mut Function) {
    body.instruction(&I::I32Load(header_field(CAPACITY_OFFSET)));
}

pub(super) fn header_field(offset: u64) -> MemArg {
    MemArg {
        offset,
        ..memory_arg(Primitive::U32)
    }
}
