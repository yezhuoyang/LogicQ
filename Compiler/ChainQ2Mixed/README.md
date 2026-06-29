# Compiler/ChainQ2Mixed

> A verified front-end + path layer + schedule layer that compiles a named, ChainQ-typed logical program down to the existing Mixed IR (`Compiler.MixedInstr`).

This layer sits between the ChainQ source language (named code families + name-addressed
ops) and the Mixed IR physical-realization layer in the LogicQ stack
(ChainQ source -> **ChainQ2Mixed** -> Mixed IR / checked primitives -> ... -> QStab/QClifford).
For each logical operation it makes the **request** (a logical op) separate from the
**realization** (which fault-tolerant path + which parallel schedule), routing every
candidate through the existing `checkInstr` / `compileScheduled?` kernel so the emitted
instructions are legal by construction. It checks *legality*, not fault tolerance: the
gadget-channel / distance / decoder boundary is inherited unchanged from the Mixed IR
(CONTRACT §3).

## What's here

| Module | Role |
|---|---|
| [Basic.lean](Basic.lean) | Umbrella; imports `Source`, `Path`, `Schedule`, `Primitive`, `Compile`, `Frame`. |
| [Source.lean](Source.lean) | `ChainQProgram` (named code-family decls + name-addressed ops); `elabProgram?` reuses the ChainQ→TypedBlock pipeline to build a `(TypedEnv × List LogicalOp)`. |
| [Path.lean](Path.lean) | `PathChoice` + fixed per-path rule `candidate?` + `compileOpWith` / `compileOpWith_sound` (single-instruction transversal / PPM-gadget / Pauli / transversal-CNOT / magic paths). |
| [Schedule.lean](Schedule.lean) | Parallel-PPM `Layer`/`Schedule`/`ScheduleMode`; stratified commutation certificate; `compileScheduled?` → proof-carrying `CompiledSchedule`; `realizeProgram?`. |
| [Primitive.lean](Primitive.lean) | The checked primitive surface `MixPrim` / `checkPrim?` → `CheckedPrimitive`, plus the (unverified) `ExternalClaim` layer and the homomorphic-CNOT bridge. |
| [Compile.lean](Compile.lean) | The ChainQ-facing source → MixIR compiler `compileChainQToMixIR?` (named addressing, `LocMap`, basis-checked ancilla pool) → `CompiledMixIR`. |
| [Frame.lean](Frame.lean) | Classical byproduct frame / feed-forward checker (`checkFrameExpr` / `checkFrameProgram`). |

## Key definitions

```lean
inductive MixPrim
  | ppm              (r : CVar) (P : MTarget)
  | ppmFragment      (s : PPM.Stmt)
  | parallelPPM      (mode : ScheduleMode) (sched : Schedule)
  | transversal      (block : Nat) (g : BoolMat)
  | transversalCNOT  (spec : TransversalCNOTSpec)
  | transversalBatch (spec : TransversalCNOTBatchSpec)
  | automorphism     (block : Nat) (M : BoolMat)
  | codeSwitch       (block : Nat) (target : Block) (cert : SwitchCert)
  | pauli            (q : LQubit) (p : PLetter)
  | magic            (ob : MagicObligation)
```
(from [Primitive.lean](Primitive.lean))

```lean
def checkPrim? (caps : List Capability) (Γ : TypedEnv) (R : PPMState) (p : MixPrim) :
    Except TypeError (CheckedPrimitive caps Γ R)
```

```lean
theorem checkPrim?_sound (caps : List Capability) (Γ : TypedEnv) (R : PPMState) (p : MixPrim)
    {cp : CheckedPrimitive caps Γ R} (_h : checkPrim? caps Γ R p = .ok cp) :
    cp.WellTyped ∧ cp.obligations = primObligations cp.prim
```

```lean
theorem compileOpWith_sound (choice : PathChoice) (caps : List Capability) (Γ : TypedEnv)
    (R : PPMState) (anc : LQubit) (r₁ r₂ r₃ : CVar) (op : Compiler.LogicalOp)
    {instr : MixedInstr} {Γ' : TypedEnv} {R' : PPMState}
    (h : compileOpWith choice caps Γ R anc r₁ r₂ r₃ op = .ok (instr, Γ', R')) :
    checkInstr caps Γ R instr = .ok (Γ', R')
```

```lean
def compileChainQToMixIR? (ws : List CapabilityWitness) (cfg : StrategyConfig) ...  -- (from Compile.lean)
```

## Example

Each value below is a real `MixPrim` checked against `cnotEnv` — the two-block bare
1-logical environment `twoBlockEnv 1` ([Primitive.lean:412](Primitive.lean#L412),
[Primitive.lean:417](Primitive.lean#L417)). `cnotSpec` / `batchSpec` are the fixtures from
[Primitive.lean:418](Primitive.lean#L418):

```lean
-- OK: a single-instruction transversal CNOT, control block-0 qubit-0 → target block-1 qubit-0,
--     with a 1×1 physical incidence map that lifts to the requested logical CNOT.
.transversalCNOT { control := ⟨0, 0⟩, target := ⟨1, 0⟩, incidence := [[true]] }

-- OK: the batched (high-rate) form — physical incidence agrees with the logical incidence.
.transversalBatch { controlBlock := 0, targetBlock := 1, incidence := [[true]], logicalIncidence := [[true]] }

-- rejected: a ZERO physical incidence that requests a logical CNOT.
--   checkTransversalCNOTBatch proves the zero map induces identity, not the requested CNOT.
.transversalBatch { controlBlock := 0, targetBlock := 1, incidence := [[false]], logicalIncidence := [[true]] }
```
A checked transversal CNOT type-checks, while a degenerate (zero-incidence) physical map
that *requests* a logical CNOT is rejected, because the checker proves the lifted map does
not induce the requested action. From [Primitive.lean](Primitive.lean) §P.7–P.8.

## Status & scope

Honest tiering (per [Compiler/CONTRACT.md](../CONTRACT.md)): **P** proved theorem, **D**
`by decide` test, **A** documented assumption, **M** missing/planned.

- **Proved (P, `propext`-clean typing soundness):** `compileOpWith_sound`,
  `realizeOp?_sound`, `realizeProgram?_sound`, `compileScheduled?_sound`,
  `checkPrim?_sound`, `compileChainQToMixIR?_sound` — every chosen path / realization /
  certified schedule / compiled program yields instructions the existing kernel accepts.
  For the transversal-CNOT family the *induced logical action* is also verified
  (`homCNOTBridge_sound`, axioms `propext, Classical.choice, Quot.sound`).
- **D (`by decide`):** ~30 positive/negative regression tests (named-op compilation;
  multi-logical direct-transversal rejected; duplicate outcome var rejected; zero-incidence
  CNOT rejected; certificate levels distinct; external-claim zero-map rejected; …).
- **A (assumed / deferred):** the Mixed gadget-channel / FT boundary — `cnot`/`cz`/
  multi-logical `H`/`S`/`measure` PPM gadgets are `idealChannel`, `magic` has no `Step`,
  and distance / decoder / fault-tolerance are deferred. Ancilla *addresses/bases* are
  checked, but ancilla state preparation stays a `logicalAncillaDeferred` obligation; the
  `commutingWithAncilla` twist-free surgery is `twistFreeSurgeryDeferred`; the chain-cert
  `ExternalClaim`s' induced action is `externalProtocolCert`.
- **M (named, not built):** `Schedule → Schedule` rewrite rules; a Mixed-IR operational
  semantics / equivalence theorem; the `Schedule → QStab` lowering (only the *coordinates*
  survive today); dimension-jump code-switch (same-arity `checkSwitch` only — a genuine
  `n`-changing jump is rejected, not faked).

This layer does **not** strengthen the inherited channel/FT boundary, and it does **not**
claim to express *all optimized programs*: the optimizer's rule choice is checked, but
program-to-program optimization is future work. GPPM and the other qLDPC paper protocols
are external checked artifacts, not `CheckedPrimitive`s.

## See also

- Parent: [Compiler/README.md](../README.md)
- Repo root: [../../README.md](../../README.md)
- Mixed-IR contract: [Compiler/CONTRACT.md](../CONTRACT.md)
- Related external-protocol checkers: [Compiler/CodeSwitch](../CodeSwitch/) (`QLDPCPapers`,
  `GPPMSemantics`, `ProductSurgery`, `DimensionJump`, `BatchedSwitch`, `QLDPCStatus`).
