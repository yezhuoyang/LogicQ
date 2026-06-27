# Compiler/Simulator

A small exact simulator for demos and regression tests.

## Syntax

```lean
Gate ::= H | S | X | Z | CNOT | CZ
State := List GInt
Layout := LQubit -> Nat
```

## Semantics

The simulator uses unnormalised Gaussian-integer state vectors.  `runGates`
executes ideal gates.  `execMixed` executes emitted Mixed instructions when the
instruction has a concrete simulator meaning.

## Typechecking Rule

This folder is not a typechecker.  It is a test harness for comparing source
ideal semantics with emitted executable fragments.

## Example

Deutsch-Jozsa, two-qubit Grover, Simon n=2, and direct H/S/Pauli compiler
examples are checked by `by decide`.
