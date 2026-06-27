# Compiler/LS2QStab

Skeleton bridge from logical PPM/surgery data to QStab.

## Syntax

```lean
SurgeryCert
ppmMeasToQStab
```

The certificate records measured parity, preserved logicals, byproduct/frame
data, merged-CSS commutation claims, detector determinism, and fault obligations.

## Typechecking Rule

`SurgeryCert.check` requires nonempty measured parity, at least one preserved
logical, deterministic detectors, and all fault obligations left deferred.

## Semantics

This is not a full lattice-surgery semantics.  It emits a small QStab skeleton
for one logical measurement.

## Example

`certZZ.check = true`; a certificate claiming distance is already certified is
rejected.
