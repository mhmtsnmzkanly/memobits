# Compile-Time Safety Notes

This document summarizes the compile-time safety work and recent changes.

## What Was Added

- **Const-eval in TypeChecker** to catch compile-time errors:
  - Constant division/modulo by zero now fails at compile-time.
  - Array constant index out-of-bounds now fails at compile-time.
- **Expanded constant folding**:
  - Integer arithmetic and comparisons.
  - Boolean logic (`&&`, `||`, `!`) and comparisons.
  - String concatenation for constant strings.
  - Float arithmetic and comparisons.
- **Warnings with source positions**:
  - Unreachable code after `return` now emits a compile-time warning.
  - Warnings include line/column when source is available.

## Behavior Summary

- **Compile-time errors**:
  - `1 / 0`, `1 % 0` (constant divisor)
  - `arr[10]` if `arr` is a fixed-size array and index is constant out-of-bounds
- **Compile-time warnings**:
  - Unreachable statements after `return`
- **Runtime errors still possible**:
  - Non-constant division by zero
  - Non-constant out-of-bounds indexing
  - User input and I/O dependent errors

## Files Touched

- `src/type_checker.rs`
- `src/main.rs`
- `docs/LANGUAGE_SPEC.md`
