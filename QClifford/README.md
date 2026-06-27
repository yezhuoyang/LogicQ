# QClifford

The physical Clifford target language.

## Syntax

```text
Gate ::= H q | S q | X q | Z q
       | CNOT c t | CZ a b
       | meas q -> r
       | ifPauli r P q
Circuit ::= Gate*
```

Gates act on physical qubits; measurements write classical bits; `ifPauli`
performs feed-forward.

## Semantics

`run` executes a circuit against a parametric `Host` that supplies the actual
state transformer for each physical Clifford and `Z` measurement.

## Typechecking Rule

This layer currently has resource counters and operational semantics, not a full
verifier.  The composition theorem is `run_append`.

## Example

```lean
QClifford.cnotFromCZ 0 1 = [.H 1, .CZ 0 1, .H 1]
```
