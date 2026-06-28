# Compiler

> The verified inter-level compiler layer: lowers source `LogicalOp` programs to the **Mixed IR** and bridges toward the physical QStab/QClifford target.

This is the compiler layer of the LogicQ stack. It sits **after** the ChainQ code families and the TypeChecker legality judgments, and **before** the QStab/QClifford physical target. The folder's own `.lean` files are **umbrella aggregators and compatibility shims** (M19/M20 strict-folder-ownership refactor); the real syntax, checker, semantics, lowering, simulator, and pass-stage bridges live in the child subfolders. The single end-to-end **wired** path is `Source LogicalOp → Mixed IR` via `compile?`; the linear `ChainQ → PPR → PPM → LS → QStab → QClifford` pipeline is partially wired and partially planned (see [CONTRACT.md](CONTRACT.md)).

## What's here

These are THIS folder's own modules — every one is an aggregator (`import` re-exporter) or a thin compatibility shim. The implementation lives in the subfolders they import.

| Module | Role |
|---|---|
| [Basic.lean](Basic.lean) | Public umbrella: `import Compiler.Basic` pulls in the whole compiler layer |
| [Mixed.lean](Mixed.lean) | Aggregator re-exporting the Mixed IR **syntax** + **checker** layers |
| [MixedSemantics.lean](MixedSemantics.lean) | Aggregator: source typing, lowering, and the operational `Step` semantics |
| [Simulator.lean](Simulator.lean) | Aggregator: the exact Gaussian-integer simulator + `Step`-aligned `execMixed` |
| [Demo.lean](Demo.lean) | Aggregator: the demo-complete `Source → compile? → Mixed → Simulator` pipeline |
| [CodeSwitch.lean](CodeSwitch.lean) | Shim: external/assumed code-switch certificates + qLDPC extension modules |
| [LogicalToPPM.lean](LogicalToPPM.lean) | Shim re-exporting the PPM-fragment evidence (now in `PPR2PPM/`) |
| [LogicalToQStab.lean](LogicalToQStab.lean) | Shim re-exporting the PPM→QStab surgery bridge (now in `LS2QStab/`) |

## Key definitions

The public compiler and its soundness theorem (defined in the `Mixed/Lower` subfolder, re-exported here):

```lean
def compile? (mode : CompileMode) (cfg : CompileConfig) (Γ : TypedEnv) (ops : List LogicalOp) :
    Except TypeError (CompiledMixed cfg.caps Γ PPMState.init) :=
```
(from [Mixed/Lower/Public.lean](Mixed/Lower/Public.lean))

```lean
theorem compileProgramLocA_sound (caps : List Capability) :
    ∀ (ops : List LogicalOp) (Γ : TypedEnv) (R : PPMState) (fresh : CVar) (m : LocMap)
      (sup : AncillaSupply)
      {prog : LogicalExec} {Γ' : TypedEnv} {R' : PPMState} {m' : LocMap} {sup' : AncillaSupply},
      compileProgramLocA caps Γ R fresh m sup ops = .ok (prog, Γ', R', m', sup') →
      checkLogicalExecAux caps Γ R prog = .ok (Γ', R')
```
(from [Mixed/Lower/Ancilla.lean](Mixed/Lower/Ancilla.lean))

```lean
def checkLogicalExecAux (caps : List Capability) :
    TypedEnv → PPMState → LogicalExec → Except TypeError (TypedEnv × PPMState)
```
(from [Mixed/Check.lean](Mixed/Check.lean))

## Example

The folder's own files are umbrella aggregators with no `def`/`theorem`/`#eval` of their own — they only re-export. The honest representative content is the public umbrella import list:

```lean
import Compiler.LogicalToPPM
import Compiler.Mixed
import Compiler.MixedSemantics
import Compiler.Simulator
import Compiler.LogicalToQStab
import Compiler.ChainQ2Mixed.Basic
import Compiler.QASM.Basic
import Compiler.QStab2QClifford.Basic
import Compiler.CodeSwitch
import Compiler.Verification.Basic
import Compiler.Verification.Compile
import Compiler.Demo
```
`import Compiler.Basic` is the single public entry point for the whole compiler layer; root-level `.lean` files are intentionally forbidden (M21). Source: [Basic.lean](Basic.lean).

## Status & scope

Honest tiers (per [CONTRACT.md](CONTRACT.md): **P** proved theorem, **D** `by decide` test, **A** documented assumption, **M** missing/planned):

- **Wired & proved (P):** `Source LogicalOp → Mixed IR` via `compile?`, sound by `compileProgramLocA_sound` / `compileProgramLocA_sound` (`propext`-clean, not "axiom-free"). The `ChainQ2Mixed` named compiler threads a checked `AncillaPool` and is `compileChainQToMixIR?_sound`.
- **Exact operationally (D):** direct H/S transversals (k=1), logical X/Z Paulis (`step_pauli_matches_exec`); `execMixed` runs these and gets stuck (`none`) on gadget channels.
- **Ideal-channel / assumed (A):** PPM gadgets (CNOT/CZ, multi-logical H/S, measure) type-check and evolve the classical store + Pauli frame, but the carrier channel (`QInterp.proj`) is UNCONSTRAINED = assumed ideal.
- **External / assumed (A):** `CodeSwitch` certificates (`structuralCheck` = shape/direction/claim only); the `QLDPCPapers/*` modules use `native_decide` (out of the core's axiom-clean scope).
- **Deferred (A) / planned (M):** magic (T-gate) discharge has no `Step` (typechecked-only); distance, fault-tolerance, decoder, and physical-channel correctness are DEFERRED; the `ChainQ→PPR`, `PPR→PPM`, `PPM→LS` passes are planned (not built). `QStab2QClifford` proves **classical-dataflow only**.

NEVER read this layer as end-to-end channel-verified: only the classical typing/dataflow edges are proved.

## See also

- Repo root: [../README.md](../README.md)
- Full correctness matrix: [CONTRACT.md](CONTRACT.md)
- [Mixed/README.md](Mixed/README.md) — target IR, checker, semantics, lowering
- [Simulator/README.md](Simulator/README.md) — exact state-vector harness and `execMixed`
- [Demo/README.md](Demo/README.md) — end-to-end examples and assumptions
- [ChainQ2Mixed/README.md](ChainQ2Mixed/README.md) — named ChainQ-facing compiler with checked ancilla pool
- [QASM/README.md](QASM/README.md) — OpenQASM-2 front-end + logical allocation
- [CodeSwitch/README.md](CodeSwitch/README.md) — external code-switch certificate skeleton
- [QStab2QClifford/README.md](QStab2QClifford/README.md) — syndrome extraction into QClifford (trace-host dataflow)
- [LS2QStab/README.md](LS2QStab/README.md) — one-measurement surgery/QStab skeleton
- [PPR2PPM/README.md](PPR2PPM/README.md) — PPR-to-PPM placeholder fragment evidence
- [ChainQ2PPR/README.md](ChainQ2PPR/README.md), [PPM2LS/README.md](PPM2LS/README.md), [LS/README.md](LS/README.md) — planned/skeleton passes
