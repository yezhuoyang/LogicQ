# ChainQ/Toric

Toric codes as cyclic-repetition hypergraph products.

## Syntax

```lean
toric d
toric? d
mkToric d
```

## Semantics

`toric d` is:

```text
HGP(repCyc d, repCyc d)
```

For fixed `d`, this materializes explicit `hx` and `hz` matrices.

## Typechecking Rule

The checked constructors reject degenerate parameters.  The code is valid when
the generated CSS checks commute.

## Example

`toric 2` has `n = 8` and `k = 2`.
