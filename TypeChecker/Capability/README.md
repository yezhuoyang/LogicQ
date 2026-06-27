# TypeChecker/Capability

Certificates for joint logical measurements.

## Syntax

```lean
inductive CapKind
  | nativeSurgery | adapterPPM | productSurgery
  | homomorphicMeasurement | bridge

structure Capability where
  kind     : CapKind
  blocks   : List BlockId
  ancN     : Nat
  connStab : BoolMat
```

## Typechecking Rule

`mkCapability?` checks the declared width of `connStab`.  The real PPM matcher
does not trust this wrapper blindly; `checkPPM` rechecks width against the actual
merged code.

## Semantics

A capability says how several code blocks may be merged for a joint logical
measurement.  The kind selects the deferred physical obligations; the algebraic
merged-code certificate is recomputed by `checkPPM`.

## Example

An adapter capability over blocks `[0, 1]` can certify a cross-block `Z tensor Z`
measurement if the merged stabilizer span contains the lifted target Pauli.
