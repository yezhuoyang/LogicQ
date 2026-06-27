# Compiler/Mixed/Lower

Source `LogicalOp` to Mixed IR lowering.

## Syntax

Important public pieces:

```lean
compileOpR
compileProgram
compileProgramLoc
compileProgramLocA
compile?
CompiledMixed
SupportedSourceProgram
```

## Typechecking Rule

`compile?` succeeds only after:

1. source operands pass `sourceWellFormed`
2. every operation has an implementation in the current environment/capabilities
3. the emitted Mixed program passes `checkLogicalExecAux`
4. the chosen `CompileMode` accepts or rejects magic obligations

## Semantics

Lowering itself is static.  The semantic boundary is recorded by
`GadgetBoundary`: exact, ideal-channel, typechecked-only, or proven-channel
(currently unused).

## Example

`compile? .executable cfg Gamma [.hGate q, .sGate q]` emits direct transversals
for a one-logical block if the transversal checks succeed.
