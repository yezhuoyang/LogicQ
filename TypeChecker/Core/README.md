# TypeChecker/Core

Typed logical blocks and binary symplectic utilities.

## Syntax

```lean
structure Block where
  n    : Nat
  stab : BoolMat
  lx   : BoolMat
  lz   : BoolMat
  live : Bool
  own  : Owned
```

`TypedBlock` carries a proof that `Block.valid = true`; `TypedEnv` is a list of
typed blocks.

## Typechecking Rule

`Block.valid` requires:

- all rows have width `2*n`
- stabilizers commute
- X and Z logical bases have the same arity
- logicals commute with stabilizers
- X/Z logical pairing is the identity
- no logical row lies in the stabilizer span
- the exposed logical count is complete: `lx.length = n - rank stab`

## Semantics

Rows use the symplectic layout `(X bits | Z bits)`.  `cssToStab` is an alias for
ChainQ materialization into this layout.

## Example

A bare logical qubit has `stab = []`, `lx = [[true,false]]`, and
`lz = [[false,true]]`.
