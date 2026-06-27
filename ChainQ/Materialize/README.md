# ChainQ/Materialize

Concrete matrix export for ChainQ codes.

## Syntax

```lean
CSSCode.xChecks
CSSCode.zChecks
CSSCode.checkMatrices
CSSCode.symplecticStabilizers
```

## Semantics

For a fixed code, `xChecks` and `zChecks` are the concrete GF(2) matrices stored
in the `CSSCode`.  `symplecticStabilizers` exports rows of width `2*n`:

```text
X row r -> r | 0
Z row r -> 0 | r
```

## Typechecking Rule

This module does not validate a code.  Use `mkCSS` or a checked family
constructor first if validity matters.

## Example

`(surface 2).symplecticStabilizers` has four rows of width ten.
