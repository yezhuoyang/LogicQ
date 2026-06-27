# Logical

Shared names for logical-level programs.

## Syntax

```lean
abbrev BlockId := Nat
structure LQubit where
  blk : BlockId
  idx : Nat
```

`LQubit` is the address of a logical qubit inside a logical block.  For example,
surface-code syntax like `q1[0]` is represented as `{ blk := blockId, idx := 0 }`.

## Rule

This folder only defines addresses.  Bounds, liveness, and ownership are checked
later by `TypeChecker.TypedEnv` and compiler source checks.

## Example

```lean
def q0 : Logical.LQubit := { blk := 0, idx := 0 }
def q1 : Logical.LQubit := { blk := 0, idx := 1 }
```
