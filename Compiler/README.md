# Compiler pipeline

The inter-level compiler of LogicQ. **The compiler target is the Mixed IR**
(`Compiler/Mixed.lean`): a logical program is a sequence of `MixedInstr`s in which
native **PPM** measurement fragments, typed **transversal** gates, logical
**automorphisms**, code **switches**, and (deferred) **magic** obligations all
*coexist*. PPM is one checked sublanguage, **not** the universal target.

## Module layout (M19/M20 refactor — code lives by ownership; old modules are aggregators)

The compiler is split into layer-/pass-oriented modules.  `Mixed.lean`,
`MixedSemantics.lean`, `Mixed/Lower.lean`, `Simulator.lean`, `Demo.lean`,
`CodeSwitch.lean`, `LogicalToPPM.lean`, and `LogicalToQStab.lean` are now
**aggregator/shim** files (a few `import` lines) that re-export the real code, so every
existing `import` keeps resolving with the same public surface.

| Module | Role |
|---|---|
| `Mixed/Syntax.lean` | The Mixed IR (`MagicKind`/`MagicObligation`/`MixedInstr`/`LogicalExec`/`LogicalOp`/`hGate2x2`/`sGate2x2`/`MixedInstr.action`/`singleLogicalBlock`/`isMagic`/`progNoMagic`). |
| `Mixed/Check.lean` | The resource-threading checker `checkInstr` / `checkLogicalExecAux` / `checkLogicalExec` + the `private` legacy M9 cost selector. |
| `Mixed/Source.lean` | Source typing: `srcOpOk` / `LogicalOp.srcAction` / `progOpNext` / `sourceOpOk` / `sourceWellFormed`. |
| `Mixed/Lower/{Op,Program,ProgramOk,LocMap,Ancilla,Public,Examples}.lean` | Lowering, split by ownership (M20): `compileOpR` (Op) → `compileProgram` (Program) → `ProgramOk*` / `LocMap*` / `Ancilla*` → `compile?`/`CompiledMixed`/`CompileMode`/`CompileConfig`/`sourceCompilable` (Public). `Mixed/Lower.lean` = aggregator. |
| `Mixed/Semantics.lean` | Operational semantics: `MixedInterp` / `ExecState` / `Step` / `Steps` + soundness/progress lemmas. |
| `Mixed.lean` | **Aggregator** → `Mixed.Syntax` + `Mixed.Check`. |
| `MixedSemantics.lean` | **Aggregator** → `Mixed.Source` + `Mixed.Lower` + `Mixed.Semantics`. |
| `Simulator/{Arithmetic,State,Gate,Algorithms,ExecMixed,Examples}.lean` | The exact Gaussian-integer simulator + `Step`-aligned `execMixed`, split by ownership (M20). `Simulator.lean` = aggregator. |
| `PPR2PPM/Basic.lean` | Proof-carrying evidence for a single PPM fragment (`CompiledPPM`). (`LogicalToPPM.lean` = shim.) |
| `LS2QStab/Basic.lean` | **Skeleton** PPM→QStab lattice-surgery bridge + surgery `SurgeryCert`. (`LogicalToQStab.lean` = shim.) |
| `CodeSwitch/Basic.lean` | **External/assumed** code-switch / dimension-jump certificate skeleton. (`CodeSwitch.lean` = shim.) |
| `Demo/{Common,Direct,Algorithms,Frames,Entangling,Families}.lean` | The demo split by topic. (`Demo.lean` = aggregator.) |

ChainQ ownership (M20): GF(2)/algebra under `ChainQ/Algebra/`, code types under
`ChainQ/Core/`, the CSS materialization/export API in `ChainQ/Materialize/Basic.lean`
(`CSSCode.xChecks`/`zChecks`/`checkMatrices`/`symplecticStabilizers`; `TypeChecker.cssToStab`
is now a thin alias of `symplecticStabilizers`).

## The unified public compiler (M15/M16)

ONE public entry, `compile? : CompileMode → CompileConfig → TypedEnv → List LogicalOp → Except …`:

- **Source checking is two-tier (M16).**  `sourceWellFormed` validates OPERANDS only
  (`validLQubit` — so a **bad index like `hGate ⟨b,99⟩` is rejected**; CNOT/CZ require
  control ≠ target; a measurement is PPM-legal).  `sourceCompilable` (= `compile?`
  succeeds) is **strictly stronger**: it additionally requires every op to have an
  available IMPLEMENTATION (a legal lowering on this `Γ`/`caps`).  `compile?` checks
  well-formedness first (clear operand error), then lowers — so it checks
  COMPILABILITY, not merely well-formedness.  `compile?_sourceOk`: success ⇒
  `sourceWellFormed`; `sourceCompilable_wellFormed`: compilable ⇒ well-formed.  A
  program can be **well-formed but not compilable** (e.g. a `CNOT` with no adapter
  capability) — rejected by `compile?` with a clear error.
- **`CompileMode`** is the magic policy: `executable` REJECTS magic obligations
  (`progNoMagic`); `moduloMagic` keeps typed `.magic` obligations.
- **`CompileConfig`** carries `caps` and the ancilla ADDRESS SEED `anc` (M16: the
  unused public `pool` field was removed; resource checking via a threaded
  `ResourcePool` = `AncillaPool` is DEFERRED — see `AncillaPool.alloc`/`alloc_valid`).
- Output is a proof-carrying **`CompiledMixed`** (program + `checkLogicalExecAux … =
  .ok …`, via `compileProgramLocA_sound`); the location map (`LocMap`) resolves
  PPM-teleportation aliases on the canonical name.

### Source `LogicalOp` → Mixed IR lowering (M18)

| Source op | Typechecker condition (`srcOpOk`/`sourceOpOk`) | Mixed IR lowering | Operational status | 
|---|---|---|---|
| `blockTransversal b g` | block `b` exists, **true 2×2** `g`, live | `transversal b g` (BLOCK-WIDE) | **EXACT** (symplectic action) |
| `hGate q` / `sGate q` | `validLQubit`, live, `k=1` | `transversal q.blk` (direct) | **EXACT** (direct fragment) |
| `hGate q` / `sGate q` | `validLQubit`, live, `k>1` | `ppm (progHAt/progSAt …)` gadget | typechecked; ideal gadget CHANNEL (teleports) |
| `xGate q` / `zGate q` | `validLQubit`, live | **`pauli q .X/.Z`** (M18 — real op) | **EXACT**: `Step.pauli` APPLIES the Pauli; run by `execMixed` (`step_pauli_matches_exec`) |
| `cnotGate c t` | valid, live, `c≠t`, adapter cap | `ppm (progCNOTAt …)` gadget | typechecked LOWERING only; ideal gadget CHANNEL |
| `czGate c t` | valid, live, `c≠t`, adapter cap | `ppm (progCZAt …)` gadget | typechecked LOWERING only; ideal CHANNEL — **EXPERIMENTAL placeholder gadget** |
| `measure r P` | PPM-legal under `caps` | `ppm (meas r P)` | typechecked; ideal projective readout |
| `tGate q` | `validLQubit`, `moduloMagic` | `magic {kind:=tGate,target:=q}` | DEFERRED (no `Step` semantics) |

**M18 — real operational semantics.**  M17 lowered `xGate`/`zGate` to a record-only
`.ppm (.frame q P)` whose `Step` left the carrier UNCHANGED, so "correctness" rested
on a convenient `loweredGates` decoder.  M18 lowers them to a real **`MixedInstr.pauli`**
whose **`Step.pauli` rule APPLIES the Pauli** to the carrier (`Step_pauli_realizes`).
`Demo.lean §5` RUNS each emitted program through **`execMixed`**, an executable
interpreter whose **`.pauli` step is PROVEN equal to the `Step.pauli` carrier update**
(`step_pauli_matches_exec`) and whose `.transversal` applies the symplectic Clifford at
the block's qubit (layout-aware, validated operationally against the source).  Note:
`execMixed` is the layout-aware per-qubit REALIZATION; it is NOT a literal
`execMixed = Step (simInterp)` equality on multi-block transversals, because the
abstract `MixedInterp.clifford` is block-LOCAL (sees the matrix, not the block index).
`execMixed` returns `none` (stuck) on anything it cannot actually run, so it never
silently drops an instruction the way `loweredGates`/`filterMap` does.

### What is EXACT vs IDEAL-CHANNEL vs DEFERRED (M18 task 3+6)

| Tier | Ops | Meaning |
|---|---|---|
| **Exact operational semantics** | direct `hGate`/`sGate` (k=1), `xGate`/`zGate` (fixed M18), selected `blockTransversal` (H/S) | emitted program RUN by `execMixed` matches the ideal simulator (the `.pauli` step proven `Step`-aligned; the Clifford step realizes the symplectic action); classifier `exactSupportedOp` (`Demo.lean §5b`) |
| **Typechecked, ideal gadget CHANNEL** | `cnotGate`/`czGate` PPM gadgets (`czGate` experimental), multi-logical `hGate`/`sGate`, `measure` | compiler genuinely lowers + type-checks; the gadget/projection CHANNEL is an assumption, NOT run by `execMixed` |
| **Deferred** | `tGate`/magic, code-switch source syntax, fault-tolerance / distance | type-checked obligation or external certificate; no operational semantics |

"**End-to-end correct**" is used ONLY for the **exact operational fragment**.  A
cross-block `CNOT` LOWERS and TYPE-CHECKS end-to-end given an **adapter capability**
(`Demo.lean §7`, `typecheckedCNOTLowering`) but this is **not** channel correctness —
`execMixed` is `none` (stuck) on the gadget.  Real ChainQ FAMILY codes (surface-2,
toric-2, an HGP, a bivariate-bicycle, a lifted-product) compile through the full
pipeline `mk<Family> → cssToTypedBlock? → TypedEnv → compile? → checkLogicalExec` on
the exact fragment (`Demo.lean §8`).

`switch` is a **Mixed-IR-only** assembly instruction (`MixedInstr.switch`) + a
`Compiler.CodeSwitch` external/assumed certificate boundary — it is **NOT a source
`LogicalOp`** (no `switchGate` constructor; a code switch is emitted by a pass).

## Evidence-carrying semantics (M12) + direct-gate syntax (M13/M14)

- **Direct-gate syntax**: `blockTransversal b g` is the **block-wide**
  direct transversal (acts on the whole block). `hGate q`/`sGate q` are
  **single-logical** ops — they lower directly to a transversal ONLY when `q`'s
  block has exactly one logical qubit (`singleLogicalBlock`, `k = 1`); on a
  multi-logical block they take a qubit-level PPM gadget or fail with an explicit
  error (never a mislabeled block-wide transversal).
- **`MagicObligation`** is a typed record (`kind`, `target`, `requiresMagicState`),
  not a string; **`AncillaPool`** is proof-carrying (allocation checks
  `validLQubit` + not-discarded + basis + ownership, not just fresh names);
  **`Compiler.CodeSwitch`** shapes the code-switch / dimension-jump certificates
  around chain maps, induced logical maps + injectivity, one-way homomorphic CNOTs,
  and the disjoint-image parallel condition (a skeleton — fault obligations deferred).
- **`Step`** is evidence-carrying: each rule has a `checkInstr … = .ok (Γ', R')`
  premise and steps to that **checked** `(Γ', R')`.
  - `Step_implies_checkInstr` — a step implies type-checker acceptance.
  - `no_step_of_checkInstr_error` / `no_step_of_not_accepted` — an instruction the
    checker **rejects** (invalid switch / raw PPM / use-after-discard) **cannot
    step**.
  - `Step_switch_uses_checked_env` — a switch steps to the env `checkSwitch`
    produced, never an arbitrary `Γ'`.
  - `ppm_step_lifts_ppm_semantics` — a `ppm` step **delegates** to `PPM.Steps`
    (the existing PPM small-step semantics): outcomes, frame/byproduct updates, and
    classical threading.
  - `Step_transversal_realizes` / `transversal_step_matches_action` — the direct
    fragment realizes the gate's **symplectic Clifford action** (preserved from M10).
  - `Step_pauli_realizes` (M18) — a `.pauli q p` step APPLIES the Pauli to the carrier
    (`s'.quantum = I.pauli p q s.quantum`); `Compiler.Sim.step_pauli_matches_exec`
    proves the executable `execMixed` realizes exactly this step.
  - `progress_*` / `progress_pauli` / `progress_ppm_progH` — no-stuck for the direct +
    Pauli + PPM subset.

## Demo assumptions (M15/M16 — read before trusting the demo)

`Demo.lean` runs Source → `compile?` → Mixed IR → Simulator on **one source AST**
(`LogicalOp`): the compiler lowers it and the simulator interprets the SAME AST
(`opGate?`).  Deutsch–Jozsa, 2-qubit Grover, and Simon n=2 are written as `LogicalOp`
programs; under the `flat 1` layout (`⟨i,0⟩ ↦ qubit i`) their `sourceGates` IS the
textbook circuit (`example : sourceGates … djConstantSrc = djConstant`).  It assumes:

- **Direct logical ops (transversal `H`/`S`) and PPM gadgets (`X`/`Z` frame updates,
  `CNOT`/`CZ`/`H`/`S` measurement gadgets) implement their intended IDEAL logical
  action.**  The simulator runs that ideal action; it does **not** re-simulate the
  physical PPM-gadget channel.  Source-vs-emitted equality is EXACT only for the
  direct transversal fragment.  `progCZAt` is a placeholder CZ gadget (shaped to
  type-check; exact measurements deferred).
- **NO circuit-level distance proof and NO full fault-tolerance claim.**
- **`CNOT`/`CZ` need an adapter capability.**  DJ-CONSTANT (only `X`+`H`) fully
  compiles (frame + direct transversal); DJ-balanced / Grover / Simon are
  **well-formed but NOT compilable** on a plain env (`sourceCompilable = false`) — the
  simulator still validates their ideal outcomes.
- **Code-switch certificates are EXTERNAL / ASSUMED** (`CodeSwitch.structuralCheck`
  checks shape/direction/injectivity-CLAIM only; distance/fault-distance/decoder
  deferred).

## What is DEFERRED (not implemented — do not assume)

- **Magic** (`T`/π·8): type-checks as a *deferred obligation* (`checkInstr` accepts
  `.magic`), but has **no operational semantics** (`Step` has no `.magic` rule —
  `no_step_magic`). `compileOpR` lowers `T` to a typed `.magic` obligation, kept by
  `compile? .moduloMagic` but **rejected by `compile? .executable`**.  Honest by
  construction — magic is type-checked, never executed.
- **Full PPM-gadget channel unitary correctness** — `Step.ppm` claims carrier/store/
  frame evolution via the PPM interface, *not* end-to-end gadget unitary equivalence
  (`PPM.Semantics` itself defers the channel).
- **Full lattice-surgery construction** — `LogicalToQStab` is a *skeleton*: one
  logical PPM measurement → a QStab `prop`+`parity`. The `SurgeryCert` records the
  surgery data (measured parity, preserved logicals, byproduct/frame, merged-CSS
  commutation, detector determinism) and lists the **deferred** obligations
  explicitly: code distance, circuit-level fault distance, decoder threshold (all
  uncertified).
- The simulator's source-vs-emitted comparison is **exact for the direct fragment**;
  PPM-gadget channels are the *ideal-gadget assumption* (labeled as such).

## Source grounding (Library/sources)

PPM-as-adaptive-channel + Pauli frame — 1506.01396; logical-measurement surgery +
detector determinism — 2407.18393; universal adapters / merged-CSS commutation +
byproducts — 2410.03628; code-switching / preserved logicals — 2510.07269,
2510.08552; fault-distance / decoder deferral methodology — 2501.14380;
stabilizer-simulation of measurement — quant-ph/0406196.
