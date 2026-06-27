# LatticeSurgery

Reserved for the full lattice-surgery and adapter IR.

## Intended Syntax

This layer should own merge, split, bridge, adapter, product-surgery, and
batched-surgery nodes.

## Intended Typechecking Rule

A surgery node should check the merged CSS matrices, measured logical Pauli,
preserved logicals, gauge handling, detector determinism, and explicit
distance/fault-distance/decoder obligations.

## Current Status

The full IR is not implemented yet.  Current skeletons live in
`Compiler/LS2QStab` and cross-block PPM capability checks live in
`TypeChecker/Judgment/PPM`.
