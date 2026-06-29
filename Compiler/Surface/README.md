# Compiler/Surface

> The LogicQ **surface language** (`.lqr`): a real text front-end that parses human-readable program text and compiles it end to end to Mixed IR.

This layer answers "can a human write a LogicQ program as *text*, and does the compiler parse and
compile it?" — yes. `Parse.lean` is a total `List Char` parser from `.lqr` surface text to the
checked `Compiler.QASM` AST, plus `compileSurfaceToMixIR?`, which lowers a surface program through
the **already-verified** `Compiler.QASM.compileQASMToMixIR?` backend (bare blocks). No new,
unverified lowering is introduced: the surface front-end is a parser + a thin adapter onto the
proven pipeline.

## What's here

| Module | Role |
| --- | --- |
| [Parse.lean](Parse.lean) | The `.lqr` text parser (`parseLqr`), register inference, the bare allocation request, and `compileSurfaceToMixIR?` (parse + allocate + compile). Reuses the QASM char-list lexing helpers, so every parse/compile test is `by decide`. |
| [Basic.lean](Basic.lean) | Public umbrella (`import Compiler.Surface.Basic`). |

## The grammar (BNF)

The accepted v0 core — the subset that parses **and** compiles today:

```
Program  ::= Stmt*                              -- statements separated by newline or ';'
Stmt     ::= 'code' Id 'as' 'Bare'              -- declare bare data blocks
           | ('H' | 'S' | 'T' | 'X' | 'Z') Qubit
           | 'CNOT' Qubit ',' Qubit
           | 'CZ'   Qubit ',' Qubit
           | 'measure' Qubit '->' Cbit
Qubit    ::= Id '[' Nat ']'                     -- e.g. q[0]
Cbit     ::= Id '[' Nat ']'                     -- e.g. c[0]
-- '// …' line comments are stripped before parsing.
```

## Example

This exact surface text parses and compiles to Mixed IR (a Bell pair on bare blocks):

```rust
code q as Bare
H q[0]
CNOT q[0], q[1]      // entangle
measure q[0] -> c[0]
measure q[1] -> c[1]
```

The front-end's own verified end-to-end claims ([Parse.lean](Parse.lean) §4–§5):

```lean
-- parsing produces exactly the expected QASM instruction AST:
example : parsesTo "X q[0]\nmeasure q[0] -> c[0]"
    [.x ⟨"q", 0⟩, .measure ⟨"q", 0⟩ ⟨"c", 0⟩] = true := by decide

-- and the program compiles end to end through the verified backend:
example : compiles? "code q as Bare\nH q[0]\nCNOT q[0], q[1]\nmeasure q[0] -> c[0]\nmeasure q[1] -> c[1]" = true := by decide
```

## Status & scope

Honest, mirroring the repo's contract tiers (P proved, D `by decide` test, A documented
assumption, M missing/planned):

- **Parses + compiles today (D).** The v0 grammar above: `code … as Bare`, the
  `H/S/T/X/Z/CNOT/CZ` gates, and `measure q[i] -> c[j]`, on bare `[[1,1,1]]` blocks. Parse-structure
  and end-to-end compile tests are `by decide` ([Parse.lean](Parse.lean) §4–§5).
- **Reuses the verified backend (P, inherited).** `compileSurfaceToMixIR?` calls
  `Compiler.QASM.compileQASMToMixIR?` — all legality checking, allocation, and MixIR emission stay
  in the proven `Compiler.ChainQ2Mixed` / `Compiler.QASM` pipeline; the surface layer adds only
  parsing.
- **Honest refusals (D).** An unknown keyword is a structured `unknownStatement`; a non-`Bare`
  code family (`code q as Surface(3)`) is a clear parse error — never silently accepted.
- **Deferred / planned (M).** Wiring richer code families into THIS front-end (so a `.lqr` program
  can name a surface/toric/lifted-product code) is the next increment; today those codes are
  declarable via the ChainQ `code … as LiftedProduct { … }` / `indexed_css { … }` macros
  ([ChainQ/SurfaceSyntax.lean](../../ChainQ/SurfaceSyntax.lean)). PPM/PPR/QStab/QClifford each have
  a BNF grammar in their `Syntax.lean` but no text parser yet (a deferred phase — see
  [DESIGN.md](../../DESIGN.md)).

## See also

- [../QASM/](../QASM/README.md) — the OpenQASM-2 front-end this layer compiles through.
- [../README.md](../README.md) — the Compiler layer overview.
- [../../README.md](../../README.md) — repository root (the "one program at every level" walkthrough).
