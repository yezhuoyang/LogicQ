# TypeChecker/Judgment/PPMProgram

Whole-program checking for PPM statements.

## Syntax

```lean
structure PPMState where
  bound : List CVar
  dead  : DeadSet

checkPPMStmt Gamma caps state stmt
checkPPMProgram Gamma caps stmt
```

## Typechecking Rule

The checker threads `PPMState` and enforces:

- every measurement is legal under `checkPPM`
- branches read only already-bound outcomes
- `frame` and `discard` target live, in-range qubits
- discarded qubits are never used again
- loop bodies do not escape new discards unsafely

## Semantics

This is static resource checking for PPM programs.  Operational stepping lives in
`PPM.Semantics`; the compiler lifts PPM steps into Mixed steps.

## Example

`discard q ;; frame q X` is rejected as use-after-discard.
