/-
  Compiler.LogicalToQStab — a SKELETON bridge from a logical PPM measurement to the
  physical QStab IR, with a SURGERY CERTIFICATE record grounded in the qLDPC
  surgery / adapter / code-switching papers.

  This is a SKELETON (M12 task 5), NOT a full qLDPC lattice-surgery implementation:
  a single native logical PPM measurement lowers to a QStab `prop` (the physical
  parity) plus a `parity` readout.  The certificate RECORDS the surgery data the
  papers require AND lists, explicitly, the obligations that remain DEFERRED
  (distance, fault distance, decoder).  We do NOT claim full lattice-surgery
  correctness.

  Grounding (Library/sources):
    * measured logical parity + detector determinism — 2407.18393 (Improved QLDPC
      Surgery: a measured logical becomes a product of merged checks; detectors are
      linear combinations of prior outcomes, deterministic under noiseless Clifford
      evolution).
    * merged CSS commutation + byproduct operators — 2410.03628 (Universal adapters:
      the merged stabilizer group commutes, `H_X H_Zᵀ = 0`; byproducts are TRACKED
      classically, not applied).
    * preserved logicals / code-switch evidence — 2510.07269, 2510.08552.
    * fault-distance / decoder deferral methodology — 2501.14380 (the obligations a
      certificate must defer: distance, R≥d fault distance, decoder threshold).
-/
import QStab.Basic
import Compiler.Mixed

namespace Compiler
open QStab Physical

/-- The status of a fault-tolerance obligation: either genuinely `certified` (a
    proof/decision discharged it) or `deferred` (an explicit, uncertified
    assumption).  M14 makes the status EXPLICIT rather than a bare Bool, so a cert
    cannot silently pretend a fault obligation is met. -/
inductive FaultStatus
  | certified | deferred
  deriving DecidableEq, Repr

/-- A fault obligation defaults to `deferred`. -/
instance : Inhabited FaultStatus := ⟨.deferred⟩

/-- The fault-tolerance obligations of a surgery/merge (M14 task 6): the code
    distance, the circuit-level fault distance, and the decoder threshold — each
    with an EXPLICIT `FaultStatus`.  All `deferred` here: we do NOT certify them. -/
structure FaultObligations where
  distance      : FaultStatus := .deferred   -- code distance ≥ d after the merge
  faultDistance : FaultStatus := .deferred   -- circuit-level fault distance (R ≥ d rounds)
  decoder       : FaultStatus := .deferred   -- modular-decoder threshold
  deriving Repr, DecidableEq

/-- Every fault obligation is honestly DEFERRED (none certified). -/
def FaultObligations.allDeferred (f : FaultObligations) : Bool :=
  f.distance == .deferred && f.faultDistance == .deferred && f.decoder == .deferred

/-- A SURGERY CERTIFICATE for a logical measurement realized by code surgery.  The
    first group records the surgery data the papers require; `deferred` lists the
    obligations that are NOT discharged here. -/
structure SurgeryCert where
  /-- (2407.18393) the measured logical parity, as a physical Pauli product. -/
  measuredParity    : QStab.PauliString
  /-- (2407.18393 Thm 1.2–1.4; 2510.07269/08552) unmeasured logicals preserved by the merge. -/
  preservedLogicals : List QStab.PauliString
  /-- (2410.03628) classical byproduct/frame corrections — TRACKED, not applied. -/
  byproductFrame    : List (Physical.PQubit × Physical.Pauli)
  /-- (2410.03628; 2510.08552 `H_X H_Zᵀ = 0`) merged CSS/stabilizer commutation — a
      recorded CLAIM (the full merged-code check is not performed in this skeleton). -/
  claimedMergedCommutes : Bool
  /-- (2407.18393) detectors deterministic under noiseless Clifford evolution — a
      recorded CLAIM; the QStab-program version IS checked by `SurgeryCert.detectorsDeterministic?`. -/
  claimedDetectorsDet   : Bool
  /-- (2407.18393 Lemma 1.8) the measured operator is irreducible — a recorded CLAIM. -/
  claimedIrreducible    : Bool
  /-- The fault-tolerance obligations, each with an explicit `FaultStatus`. -/
  faults            : FaultObligations
  deriving Repr

/-- The currently COMPUTABLE soundness checks on a certificate (structural, in this
    skeleton): the measured parity is non-empty, at least one logical is preserved,
    and the distance / fault-distance / decoder obligations are HONESTLY deferred
    (`allDeferred`).  The `claimed…` fields are NOT asserted here — they are recorded
    claims pending the full merged-code construction. -/
def SurgeryCert.check (c : SurgeryCert) : Bool :=
  ! c.measuredParity.isEmpty
  && ! c.preservedLogicals.isEmpty
  && c.faults.allDeferred

/-- Detector determinism of the LOWERED program is genuinely checkable via the
    QStab classical dataflow: under the all-`+1` (noiseless) input, the readout is a
    fixed Bool. -/
def SurgeryCert.detectorsDeterministic? (prog : QStab.Prog) (readout : QStab.QVar) : Bool :=
  QStab.evalVar prog (fun _ => false) readout == false

/-- Lower a single logical PPM measurement of physical parity `P` (optionally
    scheduled at `sched`) to a QStab program: measure `P`, then read its outcome out
    as a `parity`.  (The logical→physical elaboration of the measured operator is
    the code's `CodeMap` — a deferred detail; here `P` is given physically.) -/
def ppmMeasToQStab (sched : Option QStab.Sched) (P : QStab.PauliString) : QStab.Prog :=
  [ .prop sched P, .parity [0] ]

/-- The readout variable of a single-measurement lowering (the `parity` is stmt 1). -/
def ppmMeasToQStab_readout : QVar := 1

/-! ## A tiny NATIVE fixture: one logical Z-parity measurement. -/

/-- Measure the logical `ZZ` parity on a 2-physical-qubit interface (a tiny surgery
    readout). -/
def progZZ : QStab.Prog := ppmMeasToQStab (some ⟨0, 0⟩) (Physical.ofString "ZZ")

/-- The certificate for the `ZZ`-parity measurement.  The CHECKABLE parts are
    verified by the examples below (well-formedness + detector determinism); the
    distance / fault-distance / decoder obligations are DEFERRED (all `false`). -/
def certZZ : SurgeryCert where
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
-- The certificate's COMPUTABLE checks pass (parity nonempty, a preserved logical, all deferred obligations false).
example : certZZ.check = true := by decide

-- DETECTOR DETERMINISM of the lowered program is genuinely checkable (noiseless ⇒ fixed readout).
example : SurgeryCert.detectorsDeterministic? progZZ ppmMeasToQStab_readout = true := by decide
example : QStab.evalVar progZZ (fun _ => false) ppmMeasToQStab_readout = false := by decide
-- …and a flipped physical outcome flips the readout (the parity is non-vacuous).
example : QStab.evalVar progZZ (fun k => decide (k = 0)) ppmMeasToQStab_readout = true := by decide

-- The fault obligations are explicitly DEFERRED (none certified) — honest by construction.
example : certZZ.faults.distance = FaultStatus.deferred := by decide
example : certZZ.faults.faultDistance = FaultStatus.deferred := by decide
example : certZZ.faults.decoder = FaultStatus.deferred := by decide
example : certZZ.faults.allDeferred = true := by decide
-- A cert that (dishonestly) marked its distance CERTIFIED would FAIL `check`:
example : SurgeryCert.check { certZZ with faults := { distance := .certified } } = false := by decide
-- The recorded surgery data is the measured Z-parity with its preserved X-logical.
example : certZZ.measuredParity = [Pauli.Z, Pauli.Z] := by decide
example : certZZ.preservedLogicals = [[Pauli.X, Pauli.X]] := by decide

end Compiler
