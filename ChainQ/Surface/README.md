# ChainQ/Surface

Unrotated surface codes as hypergraph products.

## Syntax

```lean
surface d
surface? d
mkSurface d
```

## Semantics

`surface d` is not a symbolic placeholder.  It is:

```text
HGP(repOpen d, repOpen d)
```

For fixed `d`, this computes concrete `hx` and `hz` matrices.

## Typechecking Rule

`surface?` and `mkSurface` reject `d < 2`.  Validity is the usual CSS condition
inherited from the HGP construction.

## Example

`surface 2` has `n = 5`, two X-check rows, and two Z-check rows.
