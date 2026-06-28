/-
  Compiler.LS2QStab.Basic — COMPATIBILITY SHIM.

  The PPM→QStab surgery certificate + fault obligations were MIGRATED to the
  lattice-surgery IR layer (`Compiler/LS/Cert.lean`, namespace `Compiler.LS`), which
  now OWNS them.  This file re-exports them into the `Compiler` namespace so existing
  `Compiler.SurgeryCert` / `Compiler.FaultObligations` / `Compiler.ppmMeasToQStab`
  users (and `import Compiler.LogicalToQStab`) keep resolving unchanged, and keeps the
  original `ZZ`-parity fixture + its checked examples.

  See `Compiler/LS/Basic.lean` for the full lattice-surgery IR (LSIR).
-/
import Compiler.LS.Cert

namespace Compiler
open QStab Physical

-- Re-export the migrated types into the `Compiler` namespace (legacy resolution).
export Compiler.LS
  (FaultStatus FaultObligations SurgeryCert
   ppmMeasToQStab ppmMeasToQStab_readout)

/-! ## A tiny NATIVE fixture: one logical Z-parity measurement (unchanged). -/

/-- Measure the logical `ZZ` parity on a 2-physical-qubit interface (a tiny surgery
    readout). -/
def progZZ : QStab.Prog := LS.ppmMeasToQStab (some ⟨0, 0⟩) (Physical.ofString "ZZ")

/-- The certificate for the `ZZ`-parity measurement.  The CHECKABLE parts are
    verified below (well-formedness + detector determinism); the distance /
    fault-distance / decoder obligations are DEFERRED. -/
def certZZ : LS.SurgeryCert where
  measuredParity        := Physical.ofString "ZZ"
  preservedLogicals     := [Physical.ofString "XX"]   -- the X-logical preserved by a Z-parity merge
  byproductFrame        := []                          -- +1 outcome ⇒ no byproduct (track-not-apply)
  claimedMergedCommutes := true                        -- CLAIM: ZZ commutes with the data Z-stabilizers (CSS)
  claimedDetectorsDet   := true                        -- CLAIM: noiseless ⇒ deterministic (checked below)
  claimedIrreducible    := true                        -- CLAIM: a single 2-qubit Z parity is irreducible
  faults                := {}                          -- distance / fault-distance / decoder: all DEFERRED

/-! ## What IS checked (honestly). -/

-- The lowered program is WELL-FORMED (the parity references only the bound prop).
example : progZZ.wf = true := by decide
-- The certificate's COMPUTABLE checks pass (parity nonempty, a preserved logical, all deferred).
example : certZZ.check = true := by decide
-- DETECTOR DETERMINISM of the lowered program is genuinely checkable (noiseless ⇒ fixed readout).
example : LS.SurgeryCert.detectorsDeterministic? progZZ LS.ppmMeasToQStab_readout = true := by decide
example : QStab.evalVar progZZ (fun _ => false) LS.ppmMeasToQStab_readout = false := by decide
-- …and a flipped physical outcome flips the readout (the parity is non-vacuous).
example : QStab.evalVar progZZ (fun k => decide (k = 0)) LS.ppmMeasToQStab_readout = true := by decide
-- The fault obligations are explicitly DEFERRED (none certified) — honest by construction.
example : certZZ.faults.allDeferred = true := by decide
-- A cert that (dishonestly) marked its distance CERTIFIED would FAIL `check`:
example : LS.SurgeryCert.check { certZZ with faults := { distance := .certified } } = false := by decide
-- The recorded surgery data is the measured Z-parity with its preserved X-logical.
example : certZZ.measuredParity = [Pauli.Z, Pauli.Z] := by decide
example : certZZ.preservedLogicals = [[Pauli.X, Pauli.X]] := by decide

end Compiler
