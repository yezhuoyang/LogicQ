# Compiler/PPR2PPM

Placeholder for the PPR-to-PPM pass.

## Current Status

The folder currently contains proof-carrying evidence for a single PPM fragment,
not a full PPR lowering pass.

## Intended Rule

A future pass should lower Pauli-product rotations to adaptive Pauli
measurements while preserving the denotation and tracking magic resources.

## Example

Use this folder as the future home for the theorem usually shaped like:

```text
denote(PPR program) = semantics(lowered PPM program)
```
