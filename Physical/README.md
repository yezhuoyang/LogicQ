# Physical

Shared names for physical-level programs.

## Syntax

```lean
abbrev PQubit := Nat
inductive Pauli | I | X | Y | Z
```

Dense Pauli strings are lists of physical Paulis.  Missing or unknown characters
parse as `I`.

## Semantics

This folder is pure vocabulary.  Physical semantics live in `QStab` and
`QClifford`.

## Example

```lean
Physical.ofString "ZZI" = [.Z, .Z, .I]
```
