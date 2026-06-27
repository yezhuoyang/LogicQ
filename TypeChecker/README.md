# TypeChecker

Legality checks for logical operations over typed QEC blocks.

## Syntax

The checker works over:

```lean
TypedEnv          -- list of validity-carrying blocks
Capability        -- certificate data for cross-block PPMs
SwitchCert        -- symplectic map for code switching
PPM.MTarget       -- logical Pauli measurement target
```

## Typechecking Rule

All public judgments return `Except TypeError evidence`.  Success means the
checker recomputed a finite GF(2)/symplectic certificate.

Main judgments:

- `checkTransversal`
- `checkLogicalAutomorphism`
- `checkSwitch`
- `checkPPM`
- `checkPPMProgram`

## Semantics

This layer is static.  It does not execute programs; it proves that a requested
logical operation is algebraically legal for the current typed environment.

## Example

A PPM between two blocks is rejected unless a capability supplies a merged-code
certificate that preserves data stabilizers and measures the requested Pauli.

## Subfolders

- [Core](Core/README.md): blocks, typed environments, symplectic encoding.
- [Capability](Capability/README.md): cross-block measurement capabilities.
- [Judgment](Judgment/README.md): Transversal, Switch, PPM, and PPMProgram checks.
