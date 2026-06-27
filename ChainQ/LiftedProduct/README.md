# ChainQ/LiftedProduct

Lifted-product code constructor.

## Syntax

```lean
Internal.liftedProduct ell A rA nA
liftedProduct? ell A rA nA
mkLiftedProduct ell A rA nA
```

`A` is a matrix of circulant-polynomial exponent lists.

## Semantics

The constructor expands the ring-polynomial data into concrete GF(2) matrices.
The generated code has `n = (rA^2 + nA^2) * ell`.

## Typechecking Rule

Checked constructors reject shape disagreements such as `rA != A.length` and
then validate the CSS condition.

## Example

```lean
mkLiftedProduct 2 [[[0],[1]]] 1 2
```
