# Ownership validation cases

This historical checkpoint records the initial scalar-move criteria before
implicit primitive copying and borrow/share checking. The
[implementation plan](implementation-plan.md) records current ownership rules.

## Repeated reads

```mb
fn twice(value: i32) -> i32 {
    value + value
}
```

Both arithmetic operands read `value`. They must remain usable during the
expression, and the computed result is returned as a new value.

## Repeated moves

```mb
fn invalid(value: i32) {
    let first := value;
    let second := value;
}
```

The first initializer consumes `value`, even though it is an integer. The second
initializer must produce BE001 at its use of `value`. The checker must not treat
scalars as implicitly copyable.

## Branch joins

```mb
fn invalid(flag: bool, value: i32) {
    if flag { let moved := value; }
    let later := value;
}
```

`value` is unavailable on one incoming branch, so its later use is invalid.
Checking only the branch that leaves it available would be unsound.

## Loop backedges

```mb
fn invalid(value: i32) {
    loop { let moved := value; }
}
```

The first iteration consumes `value`; the next iteration cannot consume it again.
The analysis must converge across the backedge and report the original use site.

## Reinitialization

```mb
fn valid(var value: i32) {
    let previous := value;
    value = 2;
    let current := value;
}
```

A mutable owned local can receive a new value after being moved. Assignment must
consume its right operand before marking the destination available, so `value =
value` cannot restore an already moved value.

## Shadowing

```mb
fn valid(value: i32) {
    let value := value;
    let next := value;
}
```

The parameter and the shadowing binding have different local IDs. The initializer
consumes the parameter before introducing the new binding. Name reuse must not
make the new binding appear already moved.

## Evaluation order and unreachable code

Call arguments evaluate left to right. Passing one owned local twice in a call
must fail at the second argument. Unreachable control-flow blocks must not
introduce spurious move errors on paths that cannot execute. Borrow/share modes
must be rejected as unsupported by the initial checker rather than silently
accepted as owned or read access.

## Project integration gate

Project-wide ownership analysis must preserve canonical function identities across
modules. Two modules may define equally named functions with different signatures;
imports and prelude aliases must resolve to the selected declaration. Local
shadowing must retain a distinct local identity. Diagnostics for caller moves
must point to the caller source, while errors inside a callee point to its module.

Application resolution starts from entry; library resolution starts from exports.
An unrelated entry module containing an ownership error must not prevent library
analysis. Current reachability is at module granularity: unused declarations in
an included module are still checked. Wasm emission now selects the export-root function call closure independently of this source checking policy.

Invalid project resolution or type/control-flow analysis must return diagnostics
and no IR. A successful move check applies only to the supported primitive owned
subset; it does not establish borrow lifetime or aggregate memory safety.
