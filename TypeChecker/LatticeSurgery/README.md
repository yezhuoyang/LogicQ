# TypeChecker/LatticeSurgery

> Reserved namespace for future lattice-surgery and adapter legality checks — currently a documentation stub with no Lean modules of its own.

This folder is a placeholder in the TypeChecker layer of the LogicQ stack (front-end ChainQ code families -> **TypeChecker legality** -> Compiler Mixed/LS IR -> QStab/QClifford physical target). It is intended to eventually host type-checker judgments specific to lattice-surgery merges/splits and code adapters. As of now it contains **only this README** — the working surgery logic lives in the sibling layers linked below, and nothing in this directory is wired in or proved.

## What's here

This folder currently has **no `.lean` modules of its own** and no subdirectories.

| Module | Role |
| --- | --- |
| _(none yet)_ | Reserved for future lattice-surgery / adapter legality judgments |

Where the real work currently lives (not in this folder):

| Location | Role |
| --- | --- |
| [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean) | Cross-block PPM capability matcher `checkPPM` (the present surgery-adjacent legality path) |
| [`../../Compiler/LS2QStab/Basic.lean`](../../Compiler/LS2QStab/Basic.lean) | Compatibility shim re-exporting the PPM->QStab surgery certificate into the `Compiler` namespace |
| `../../Compiler/LS/` | The lattice-surgery IR (LSIR) that now owns `SurgeryCert` / `FaultObligations` |

## Key definitions

This folder defines no Lean symbols. The surgery-relevant definitions it will eventually complement live in the linked files, e.g. the proof-carrying capability matcher in [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean):

```lean
def checkPPM (Γ : TypedEnv) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM :=
```

and its honest record of per-capability **deferred** obligations (same file):

```lean
def ppmObligations : CapKind → List String
  | .nativeSurgery          => ["merged-code distance", "fault distance R ≥ d", "decoder for merged syndrome"]
  | .adapterPPM             => ["relative expansion β_d ≥ 1", "thickening L", "decoder for merged code"]
```

## Example

There is no example in this folder (it is a stub). The closest representative checked example is the tiny logical `ZZ`-parity surgery fixture in the sibling shim [`../../Compiler/LS2QStab/Basic.lean`](../../Compiler/LS2QStab/Basic.lean):

```lean
-- The lowered program is WELL-FORMED (the parity references only the bound prop).
example : progZZ.wf = true := by decide
-- The certificate's COMPUTABLE checks pass (parity nonempty, a preserved logical, all deferred).
example : certZZ.check = true := by decide
-- DETECTOR DETERMINISM of the lowered program is genuinely checkable (noiseless ⇒ fixed readout).
example : LS.SurgeryCert.detectorsDeterministic? progZZ LS.ppmMeasToQStab_readout = true := by decide
-- The fault obligations are explicitly DEFERRED (none certified) — honest by construction.
example : certZZ.faults.allDeferred = true := by decide
```

These `by decide` checks (contract tier **D**) verify well-formedness, the certificate's computable checks, and detector determinism for a single logical Z-parity merge, while the distance / fault-distance / decoder obligations stay **deferred**.

## Status & scope

- **Stub / planned (tier M).** This directory contains no Lean code and exposes no definitions, theorems, or `#eval`/`decide` checks. Nothing here is proved or wired.
- The surgery work it is reserved to extend is honest about its own scope: the PPM->QStab certificate in the [`Compiler/LS2QStab`](../../Compiler/LS2QStab/Basic.lean) shim checks well-formedness and detector determinism (`by decide`, tier **D**), but **distance, fault-distance, and decoder obligations are explicitly DEFERRED** (tier **A**), and `ppmObligations` in [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean) records these as documented, paper-faithful deferred obligations.
- No channel-correctness, fault-tolerance, distance, or operational-equivalence claim is made by this folder.

## See also

- [TypeChecker README](../README.md) — parent layer (legality / capability matching)
- [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean) — the present cross-block PPM capability matcher
- [`../../Compiler/LS2QStab/Basic.lean`](../../Compiler/LS2QStab/Basic.lean) — PPM->QStab surgery certificate shim
- [`../../Compiler/CONTRACT.md`](../../Compiler/CONTRACT.md) — proof-tier conventions (P / D / A / M)
