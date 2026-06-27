# ChainQ/Algebra

The small GF(2) algebra kernel used by ChainQ and the typechecker.

## Syntax

```lean
abbrev BoolVec := List Bool
abbrev BoolMat := List BoolVec
```

Matrices are ordinary lists.  The code uses explicit shape predicates when a
silent `List.zip` truncation would be dangerous.

## Semantics

`true` is 1 and `false` is 0.  `dotBit`, `gemmT`, `matMul`, `transpose`,
`rank`, `kernelBasis`, and `inSpan` implement finite GF(2) linear algebra.

## Typechecking Rule

Use `hasShape`, `matrixWellShaped`, `sameWidth`, and `compatibleMul` before
trusting a matrix calculation.  Checked wrappers such as `quotientBasis?` and
`gf2Inv?` reject malformed inputs.

## Example

```lean
ChainQ.GF2.orthogonal hx hz = true
```

means every row of `hx` is GF(2)-orthogonal to every row of `hz`.
