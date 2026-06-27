# TypeChecker/Judgment/PPM

Logical Pauli measurement checking.

## Syntax

```lean
checkPPM Gamma caps target
```

`target` is a `PPM.MTarget`, a list of logical qubits paired with `X`, `Y`, or
`Z`.

## Typechecking Rule

The checker requires:

- target is nonempty
- target has one or two factors and no duplicate logical qubit
- every logical index is in range
- each restricted block representative commutes with that block's stabilizers
- cross-block targets have a matching capability
- the merged stabilizer code commutes, preserves data stabilizers, and contains
  the lifted target Pauli

## Semantics

Success is evidence that the requested logical measurement is implementable by a
native or capability-backed PPM construction.  Fault-distance and decoder
obligations remain listed as obligations.

## Example

A single-block logical Z measurement succeeds natively.  A cross-block `Z tensor
Z` measurement succeeds only with a capability whose connection stabilizer spans
the lifted target.
