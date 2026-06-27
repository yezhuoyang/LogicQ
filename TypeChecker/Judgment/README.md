# TypeChecker/Judgment

The logical-operation judgments.

## Syntax

Each subfolder owns one judgment:

- [Transversal](Transversal/README.md): local gates and automorphisms.
- [Switch](Switch/README.md): code switching.
- [PPM](PPM/README.md): logical Pauli measurement capability matching.
- [PPMProgram](PPMProgram/README.md): whole PPM statement checking.

## Rule

Judgments consume a `TypedEnv`; malformed blocks are unrepresentable here.
Boundary functions validate raw `Env` values before calling the typed judgment.

## Semantics

This folder is static.  Runtime semantics live in `PPM` and `Compiler/Mixed`.

## Example

`checkTransversal Gamma b H` succeeds only if the tensor-power H map is
symplectic and preserves the block stabilizers.
