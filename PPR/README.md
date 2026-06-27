# PPR

Pauli-product rotations over logical qubits.

## Syntax

```text
PauliString ::= (LQubit -> X|Y|Z)*
Angle       ::= pi | pi/2 | pi/4 | pi/8
Phase       ::= +/- Angle
Rot         ::= Phase * PauliString
RotProg     ::= Rot*
```

`I` is represented by leaving a qubit out of the sparse Pauli string.

## Semantics

`Rot.denote` maps a rotation to:

```text
cos(phi) * I + i sin(phi) * P
```

`RotProg.denote` multiplies rotations left-to-right.  The theorem
`denote_append` is the composition law.

## Typechecking Rule

`RotProg.wf` checks that each Pauli string mentions a logical qubit at most once.

## Example

```lean
PPR.rotT { blk := 0, idx := 0 }      -- +pi/8 about Z
PPR.rotZZ q0 q1      -- +pi/8 about Z tensor Z
```
