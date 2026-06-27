# PPM

QMeas-style adaptive Pauli-product measurement programs over logical qubits.

## Syntax

```text
MTarget ::= (LQubit -> X|Y|Z)*
Stmt    ::= meas r MTarget
          | frame q (X|Y|Z)
          | discard q
          | ite r then else
          | forLoop n body
          | skip
          | seq s t
          | abort
```

The native measurement alphabet is strict: a target has one or two factors and
does not repeat a logical qubit.

## Semantics

`PPM.Step` is a small-step semantics over:

```text
quantum carrier, classical store, Pauli frame, remaining statement
```

Measurements call a parametric projector `QInterp.proj`; frames compose in the
classical Pauli frame; `abort` is stuck.

## Typechecking Rule

PPM program legality is checked in `TypeChecker.Judgment.PPMProgram`.  It
requires legal measurements, bound classical outcomes for branches, and no use
after discard.

## Example

`progHAt q anc r1 r2` is the Hadamard measurement gadget.  Its four byproduct
branches are proven by the PPM step rules.
