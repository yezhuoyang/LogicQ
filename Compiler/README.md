# Compiler

The implemented compiler lowers source `LogicalOp` programs to the Mixed IR.

## Syntax

Source operations and Mixed instructions are defined in `Compiler/Mixed/Syntax`:

```text
LogicalOp  ::= measure | hGate | sGate | cnotGate | tGate
             | blockTransversal | xGate | zGate | czGate

MixedInstr ::= ppm | transversal | automorphism | switch | magic | pauli
```

## Typechecking Rule

The public compiler is:

```lean
compile? mode cfg Gamma ops
```

It first checks source operands with `sourceWellFormed`, then lowers with
`compileProgramLocA`, then checks the resulting Mixed program with
`checkLogicalExecAux`.

## Semantics

Mixed programs have an evidence-carrying small-step semantics in
`Compiler/Mixed/Semantics`.  The executable simulator `execMixed` runs the exact
direct/Pauli fragment and gets stuck on gadget channels it cannot model.

## Correctness Boundary

Read [CONTRACT.md](CONTRACT.md) for the full matrix.  Short version:

- exact: direct H/S transversals and logical X/Z Paulis
- ideal-channel: PPM gadgets such as CNOT/CZ/H/S fallback
- typechecked-only: magic obligations
- external/assumed: code-switch protocol certificates

## Subfolders

- [Mixed](Mixed/README.md): target IR, checker, semantics, lowering.
- [Simulator](Simulator/README.md): exact state-vector test harness and `execMixed`.
- [Demo](Demo/README.md): end-to-end examples and assumptions.
- [CodeSwitch](CodeSwitch/README.md): external code-switch certificate skeleton.
- [PPR2PPM](PPR2PPM/README.md): PPR-to-PPM placeholder fragment evidence.
- [LS2QStab](LS2QStab/README.md): one-measurement surgery/QStab skeleton.
- [ChainQ2PPR](ChainQ2PPR/README.md), [PPM2LS](PPM2LS/README.md),
  [QStab2QClifford](QStab2QClifford/README.md): planned passes.
