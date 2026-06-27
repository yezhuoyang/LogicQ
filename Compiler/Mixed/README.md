# Compiler/Mixed

The implemented compiler target.

## Syntax

```text
MixedInstr ::= ppm Stmt
             | transversal block gate2x2
             | automorphism block symplecticMatrix
             | switch block targetBlock cert
             | magic obligation
             | pauli logicalQubit PLetter
```

Source `LogicalOp` lives here too; it is the small Lean DSL compiled by
`compile?`.

## Typechecking Rule

`checkInstr` threads a `TypedEnv` and `PPMState`.  It delegates to:

- PPM program checker for `.ppm`
- transversal and automorphism judgments for direct gates
- switch checker for `.switch`
- live/in-range checks for `.pauli`
- no execution check for `.magic`, which is a typed obligation

## Semantics

`Step` is evidence-carrying: each runtime step includes a proof that
`checkInstr` accepted the instruction.  There is no `Step` rule for magic.

## Example

`hGate q` lowers directly to `.transversal` only when the block has exactly one
logical qubit.  Otherwise it must use a PPM gadget or fail.

See [Lower](Lower/README.md) for the compiler path.
