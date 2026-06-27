# ChainQ

The front-end code type system.

## Syntax

ChainQ has three code views:

```text
ChainComplex : C2 --d2--> C1 --d1--> C0
CSSCode      : n, hx, hz
StabilizerCode : n, Pauli generator strings
```

Parametric families such as surface, toric, HGP, BB, and lifted-product codes
construct concrete `CSSCode` values.

## Typechecking Rule

- `ChainComplex.valid` means the matrices have the declared shape and
  `d2 * d1 = 0`.
- `CSSCode.valid` means `Hx * Hz^T = 0`.
- `StabilizerCode.valid` means every generator has length `n` and all generators
  commute.

The theorem `chainComplex_css` connects the first two rules.

## Semantics

For fixed parameters, a family constructor computes concrete GF(2) matrices.
`ChainQ.Materialize` exports `xChecks`, `zChecks`, `checkMatrices`, and
`symplecticStabilizers`.

## Example

```lean
ChainQ.surface 2     -- n = 5, with explicit hx/hz rows
ChainQ.mkSurface 2   -- checked constructor
```

## Subfolders

- [Algebra](Algebra/README.md): GF(2) matrix kernel.
- [Core](Core/README.md): code types, chain complexes, parameters, errors.
- [Materialize](Materialize/README.md): concrete check/stabilizer export.
- Code families: [HGPCode](HGPCode/README.md), [Surface](Surface/README.md),
  [Toric](Toric/README.md), [BBCode](BBCode/README.md),
  [LiftedProduct](LiftedProduct/README.md), [ColorCode](ColorCode/README.md).
- [Checked](Checked/README.md): validity-carrying constructors.
