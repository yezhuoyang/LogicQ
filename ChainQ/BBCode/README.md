# ChainQ/BBCode

Bivariate bicycle code constructor.

## Syntax

```lean
Internal.bb ell m A B
bb? ell m A B
mkBB ell m A B
```

`A` and `B` are lists of bivariate monomial exponents.

## Semantics

The constructor builds circulant/block-circulant GF(2) matrices and returns a
CSS code.  The current implementation is finite and concrete: fixed parameters
produce explicit `hx` and `hz`.

## Typechecking Rule

The checked constructors reject zero dimensions and empty polynomial data, then
validate the CSS condition.

## Example

```lean
mkBB 2 2 [(0,0),(1,0)] [(0,0),(0,1)]
```
