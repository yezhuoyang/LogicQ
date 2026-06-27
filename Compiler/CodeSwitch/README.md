# Compiler/CodeSwitch

External code-switch and dimension-jump certificate records.

## Syntax

```lean
PhysMap
ChainMapCert
LogicalInjectionCert
HomomorphicCNOTCert
SwitchProtocolCert
```

## Typechecking Rule

`structuralCheck` checks shapes, direction, disjointness, and claimed injection
flags.  It does not prove distance, decoder thresholds, or full chain-map
correctness.

## Semantics

This is a certificate boundary, not an executable semantics.  The symplectic
switch checker lives in `TypeChecker/Judgment/Switch`.

## Example

`goodSwitch.structuralCheck = true`; a self-CNOT or dishonest distance-certified
claim is rejected.
