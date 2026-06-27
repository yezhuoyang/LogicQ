# QStab

Physical stabilizer-measurement dataflow.

## Syntax

```text
Stmt ::= prop optionalSchedule PauliString
       | parity [QVar]
Prog ::= Stmt*
```

Each statement binds the next classical variable.  `prop` records a physical
Pauli measurement; `parity` XORs earlier variables.

## Semantics

`eval` computes the classical values of all bound variables from the physical
measurement outcomes.  The quantum back-action is intentionally outside this
small dataflow semantics.

## Typechecking Rule

`Prog.wf` rejects forward references: a parity may only read variables that have
already been bound.

## Example

`progReadout` measures `ZZI`, `IZZ`, repeats them, and forms syndrome parities.
A flipped first measurement flips the corresponding syndrome but not the final
logical-output parity.
