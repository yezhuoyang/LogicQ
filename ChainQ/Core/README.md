# ChainQ/Core

Core code types and their static rules.

## Syntax

```lean
structure CSSCode where
  n  : Nat
  hx : BoolMat
  hz : BoolMat

structure ChainComplex where
  nFaces nEdges nVerts : Nat
  d2 : BoolMat
  d1 : BoolMat
```

`StabilizerCode` stores dense Pauli generator strings.

## Typechecking Rule

- `CSSCode.valid`: every row has width `n`, and `orthogonal hx hz`.
- `ChainComplex.valid`: `d2` and `d1` have the declared shapes, and
  `matMul d2 d1 = 0`.
- `CSSLogicalBasis.valid`: checks shape, commutation with stabilizers,
  non-stabilizer status, and canonical X/Z pairing.

## Semantics

`ChainComplex.toCSS` elaborates the chain complex to CSS checks:

```text
hx = d2
hz = transpose d1
```

`CSSCode.k` computes the number of logical qubits by rank.

## Example

`square.valid = true` and `square.toCSS.cssCondition = true` are decided in
`ChainComplex.lean`.
