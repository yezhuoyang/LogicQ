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

There is no example in this folder (it is a stub). The closest representative checked value is the tiny logical `ZZ`-parity surgery fixture in the sibling shim [`../../Compiler/LS2QStab/Basic.lean`](../../Compiler/LS2QStab/Basic.lean). The fixture is one logical `ZZ`-parity measurement on a 2-physical-qubit interface — `progZZ = LS.ppmMeasToQStab (some ⟨0,0⟩) (ofString "ZZ")`, which is just the QStab program:

```lean
-- progZZ : the lowered surgery program (one measured Z-parity + its readout parity).
[ .prop (some ⟨0,0⟩) (ofString "ZZ")    -- measure the logical ZZ parity (binds QVar 0)
, .parity [0] ]                          -- the readout parity (QVar 1)
```

and the surgery certificate it carries ([`../../Compiler/LS2QStab/Basic.lean:32`](../../Compiler/LS2QStab/Basic.lean#L32)):

```lean
-- certZZ : LS.SurgeryCert — the surgery data for the ZZ-parity merge.
{ measuredParity        := [Pauli.Z, Pauli.Z]      -- the measured Z-parity (ofString "ZZ")
  preservedLogicals     := [[Pauli.X, Pauli.X]]    -- the X-logical preserved by a Z-parity merge
  byproductFrame        := []                       -- +1 outcome ⇒ no byproduct (track-not-apply)
  claimedMergedCommutes := true                     -- CLAIM: ZZ commutes with the data Z-stabilizers (CSS)
  claimedDetectorsDet   := true                     -- CLAIM: noiseless ⇒ deterministic
  claimedIrreducible    := true                     -- CLAIM: a single 2-qubit Z parity is irreducible
  faults                := {} }                      -- distance / fault-distance / decoder: all DEFERRED
```

For this fixture the computable surgery checks (contract tier **D**) hold — the lowered `progZZ` is well-formed, `certZZ`'s computable checks pass (parity nonempty, a preserved logical, all faults deferred), detector determinism is genuine (noiseless ⇒ fixed readout, and a flipped physical outcome flips the readout), and the fault obligations are explicitly deferred (none certified):

```lean
-- OK: well-formed, checks pass, deterministic, faults all deferred.
progZZ.wf
certZZ.check
LS.SurgeryCert.detectorsDeterministic? progZZ LS.ppmMeasToQStab_readout
certZZ.faults.allDeferred
-- rejected: a cert that dishonestly marked its distance CERTIFIED fails `check`.
LS.SurgeryCert.check { certZZ with faults := { distance := .certified } }
```

These computable checks verify well-formedness, the certificate's computable checks, and detector determinism for a single logical Z-parity merge, while the distance / fault-distance / decoder obligations stay **deferred**.

## Status & scope

- **Stub / planned (tier M).** This directory contains no Lean code and exposes no definitions, theorems, or `#eval`/`decide` checks. Nothing here is proved or wired.
- The surgery work it is reserved to extend is honest about its own scope: the PPM->QStab certificate in the [`Compiler/LS2QStab`](../../Compiler/LS2QStab/Basic.lean) shim checks well-formedness and detector determinism (`by decide`, tier **D**), but **distance, fault-distance, and decoder obligations are explicitly DEFERRED** (tier **A**), and `ppmObligations` in [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean) records these as documented, paper-faithful deferred obligations.
- No channel-correctness, fault-tolerance, distance, or operational-equivalence claim is made by this folder.

## See also

- [TypeChecker README](../README.md) — parent layer (legality / capability matching)
- [`../Judgment/PPM/Check.lean`](../Judgment/PPM/Check.lean) — the present cross-block PPM capability matcher
- [`../../Compiler/LS2QStab/Basic.lean`](../../Compiler/LS2QStab/Basic.lean) — PPM->QStab surgery certificate shim
- [`../../Compiler/CONTRACT.md`](../../Compiler/CONTRACT.md) — proof-tier conventions (P / D / A / M)
