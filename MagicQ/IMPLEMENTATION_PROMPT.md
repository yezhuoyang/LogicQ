# Prompt For The First MagicQ Implementation Agent

You are implementing the first real MagicQ pass in the LogicQ repository.

Read these files first:

- `MagicQ/DESIGN_PLAN.md`
- `MagicQ/README.md`
- `ChainQ/README.md`
- `TypeChecker/Core/Block.lean`
- `TypeChecker/Judgment/Switch/Check.lean`
- `Compiler/Mixed/Syntax.lean`
- `Compiler/Mixed/Lower/Op.lean`

Also inspect the paper/source references only as needed:

- `Library/sources/2409.17595__Magic_state_cultivation_growing_T_states_as_cheap_as_CNOT_gates/main.tex`
- `Library/sources/quant-ph_0403025__Universal_Quantum_Computation_with_ideal_Clifford_gates_and_noisy_ancillas/final.tex`
- `Library/source_repos/magic-state-cultivation-zenodo/src/cultiv/_construction/_integration.py`
- `Library/source_repos/magic-state-cultivation-zenodo/testdata/factory_scripts/o1_d3_t15_q5_reedmuller.dat`

## Core Direction

MagicQ should be a real source language for magic-state protocols, not just a
collection of Lean helper functions. Define a clear abstract syntax tree for
MagicQ programs and operations. Do not implement MagicQ as embedded Lean syntax,
Lean notation, or Lean-term-as-program. The first version can be an explicit AST
in Lean datatypes plus documented intended surface syntax.

Reuse the existing LogicQ/ChainQ/TypeChecker machinery wherever possible. Define
new structures only when the existing system does not already have the concept.
Likely new concepts include magic resources, cultivation carriers, postselection
conditions, decoder/gap conditions, and protocol-specific external obligations.

The most important first feature is high-level checking. When a user writes a
MagicQ program for magic-state cultivation, the checker should validate the
parts that can be checked at the highest logical/type level, using ChainQ and
the existing type system:

- the carrier code/block exists and is live/owned when transformed,
- logical observables mentioned by a check/measurement are well-formed,
- a requested logical measurement is compatible with the carrier's exposed
  logical basis/capabilities,
- code growth/switching preserves logical arity and exposes the promised output,
- postselection predicates refer to detectors/syndromes produced by prior ops,
- linear magic resources are consumed exactly once,
- the protocol does not return a magic state unless its declared basis/carrier
  and quality obligations have been established.

Do not attempt to verify full stochastic fault tolerance or decoder performance
in this pass. Record those as explicit deferred obligations.

## First Implementation Scope

Create the first MagicQ Lean modules and wire them into the build:

- `MagicQ/Syntax.lean`
- `MagicQ/Check.lean`
- `MagicQ/Library/ReedMuller15.lean`
- `MagicQ/Library/Cultivation.lean`
- `MagicQ/Basic.lean`

Update `lakefile.toml` only if needed so `MagicQ.*` modules are included in the
library build.

### Syntax

Define AST/data structures for:

- `MagicBasis`, including at least `T`, `Tdg`, `Y`, and `A0`.
- `MagicQuality`, with optional fields for raw error, output error, success
  probability, code distance, fault distance, and a list of deferred claims.
- `Carrier`, reusing `TypeChecker.BlockId`, `TypeChecker.Block`, or
  `TypeChecker.TypedBlock` references instead of inventing a parallel code
  representation.
- `MagicState` and a linear `MagicEnv`.
- `PostselectCond`, including full detector postselection, syndrome equality,
  tagged detector postselection, and decoder-gap threshold.
- `ProtocolOp`, with constructors for injection, logical check/measurement,
  grow/switch/graft, stabilize rounds, postselect, 15-to-1 distillation,
  discard/failure, and output.
- `Protocol`, as a named list of `ProtocolOp`s with parameters/spec metadata.

Keep the syntax general enough for both:

- Magic state cultivation: injection, check-grow-stabilize, escape, output.
- Standard 15-to-1: consume 15 inputs, syndrome/postselect/decode, output 1.

### Checker

Implement a small high-level checker that threads:

```text
TypedEnv x MagicEnv x CheckState -> ProtocolOp -> Except TypeError (...)
```

or define a MagicQ-specific error type if the existing `TypeError` cannot
express the issue cleanly. Prefer reusing existing errors where they fit.

The checker should perform concrete checks now:

- block lookup and liveness/ownership using `TypedEnv.block?`,
- logical index/count checks using existing block logical basis fields,
- simple code-switch/grow shape checks by calling or mirroring
  `TypeChecker.Judgment.Switch` where possible,
- postselection-scope checks against tracked detector/syndrome names,
- exact input/output arity for 15-to-1,
- exact linear consumption of magic input resources.

It should produce a checked protocol summary containing:

- output magic resources,
- consumed resources,
- final carrier/block ids,
- deferred obligations.

### Library Protocols

In `MagicQ/Library/ReedMuller15.lean`, add the punctured Reed-Muller vectors
from Bravyi-Kitaev:

- four linear generators `[x_j]`,
- six quadratic generators `[x_i x_j]`,
- small rank/length examples where feasible.

Define a first `rm15To1` protocol AST that consumes 15 `T` states and returns
one `T` state on success, with symbolic/deferred quality facts:

- success probability formula as a string or structured placeholder,
- threshold `eps < 0.141`,
- leading output error `35 * eps^3`.

In `MagicQ/Library/Cultivation.lean`, define a first `cultivateT` protocol AST
with parameters:

- `d1`, `d2`, `r1`, `r2`,
- injection style, defaulting to unitary,
- early full postselection,
- escape/gap postselection as a deferred decoder obligation.

For this first pass, it is acceptable for color-code and grafted-matchable code
objects to be named external carriers or checked placeholders, as long as the
checker records the external obligations honestly and does not pretend to prove
missing ChainQ color-code facts.

## Tests / Examples

Add small examples in Lean that are cheap to build:

- `rm15To1` rejects fewer than 15 inputs.
- `rm15To1` accepts exactly 15 compatible `T` resources and produces one output.
- a cultivation protocol with valid placeholder carrier names produces one
  output and records deferred growth/escape obligations.
- a postselection condition referring to an unknown detector/syndrome is rejected.
- an output before required quality/carrier obligations is rejected.

Run at least:

```powershell
lake build MagicQ.Basic
```

If the broader repo is already dirty, do not revert unrelated changes.

## Non-Goals For This Pass

- No parser.
- No custom Lean notation for MagicQ source programs.
- No low-level Stim/circuit generation.
- No proof of color-code distance or cultivation stochastic correctness.
- No full gate-teleportation discharge of `Compiler.Mixed.MagicObligation` yet.

The end state should be a compiling high-level MagicQ AST plus checker skeleton
that is genuinely useful for rejecting malformed cultivation/distillation
programs at the logical/type level.
