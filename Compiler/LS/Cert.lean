/-
  Compiler.LS.Cert — surgery certificates and fault obligations (migrated here from
  `Compiler/LS2QStab/Basic.lean`, M19's PPM→QStab skeleton, so the LS layer OWNS them).

  These are the honest-deferral primitives the lattice-surgery IR needs:
    * `FaultStatus` — a fault obligation is `certified` (discharged) or `deferred`.
    * `FaultObligations` — distance / fault-distance / decoder, each with a status.
    * `SurgeryCert` — the logical→physical measurement certificate (the recorded
      surgery data PLUS the explicitly-deferred obligations).
    * `ppmMeasToQStab` — a single physical-parity measurement lowered to a QStab prog.

  `Compiler/LS2QStab/Basic.lean` now re-exports these into the `Compiler` namespace, so
  existing `Compiler.SurgeryCert` / `Compiler.FaultObligations` users keep resolving.

  Mathlib-free.  Grounding (Library/sources): 2407.18393 (measured logical parity +
  deterministic detectors), 2410.03628 (merged-CSS commutation, tracked byproducts),
  2510.07269/08552 (preserved logicals / code-switch), 2501.14380 (deferred
  distance/fault-distance/decoder obligations).
-/
import QStab.Basic

namespace Compiler.LS
open QStab Physical

/-- The status of a fault-tolerance obligation: genuinely `certified` (a
    proof/decision discharged it) or `deferred` (an explicit, uncertified
    assumption).  Explicit, not a bare Bool, so a cert cannot silently pretend. -/
inductive FaultStatus
  | certified | deferred
  deriving DecidableEq, Repr

instance : Inhabited FaultStatus := ⟨.deferred⟩

/-- The fault-tolerance obligations of a surgery/merge: code distance, circuit-level
    fault distance, decoder threshold — each with an EXPLICIT `FaultStatus`.  Defaults
    to all `deferred`: this layer does NOT certify them. -/
structure FaultObligations where
  distance      : FaultStatus := .deferred
  faultDistance : FaultStatus := .deferred
  decoder       : FaultStatus := .deferred
  deriving Repr, DecidableEq

/-- Every fault obligation is honestly DEFERRED (none certified). -/
def FaultObligations.allDeferred (f : FaultObligations) : Bool :=
  f.distance == .deferred && f.faultDistance == .deferred && f.decoder == .deferred

/-- A SURGERY CERTIFICATE for a logical measurement realised by code surgery.  The
    first group records the surgery data the papers require; `faults` lists the
    obligations NOT discharged here. -/
structure SurgeryCert where
  measuredParity        : QStab.PauliString               -- (2407.18393) measured logical parity, physically
  preservedLogicals     : List QStab.PauliString          -- (2407.18393; 2510.07269/08552) unmeasured logicals preserved
  byproductFrame        : List (Physical.PQubit × Physical.Pauli)  -- (2410.03628) classical byproduct frame — TRACKED, not applied
  claimedMergedCommutes : Bool                            -- (2410.03628; 2510.08552) merged-CSS commutation — a recorded CLAIM
  claimedDetectorsDet   : Bool                            -- (2407.18393) deterministic detectors — a CLAIM (QStab version IS checkable below)
  claimedIrreducible    : Bool                            -- (2407.18393) measured operator irreducible — a CLAIM
  faults                : FaultObligations                -- the deferred fault obligations
  deriving Repr

/-- The currently COMPUTABLE soundness checks (structural): the measured parity is
    non-empty, at least one logical is preserved, and the distance / fault-distance /
    decoder obligations are HONESTLY deferred.  The `claimed…` fields are NOT asserted
    — they are recorded claims pending the full merged-code construction. -/
def SurgeryCert.check (c : SurgeryCert) : Bool :=
  ! c.measuredParity.isEmpty
  && ! c.preservedLogicals.isEmpty
  && c.faults.allDeferred

/-- Detector determinism of a LOWERED program, checked via the QStab classical
    dataflow under the all-`+1` (noiseless) input.  NON-VACUOUS: requires the program
    to be WELL-FORMED and the `readout` var to be IN RANGE (`< prog.length`) before
    evaluating — otherwise `QStab.evalVar` would silently default a missing/out-of-range
    var to `false` and a malformed readout would masquerade as "deterministic".  An
    invalid program / out-of-range readout returns `false`. -/
def SurgeryCert.detectorsDeterministic? (prog : QStab.Prog) (readout : QStab.QVar) : Bool :=
  prog.wf && decide (readout < prog.length) && (QStab.evalVar prog (fun _ => false) readout == false)

/-- Lower a single logical PPM measurement of physical parity `P` (optionally
    scheduled) to a QStab program: measure `P`, then read its outcome as a `parity`. -/
def ppmMeasToQStab (sched : Option QStab.Sched) (P : QStab.PauliString) : QStab.Prog :=
  [ .prop sched P, .parity [0] ]

/-- The readout variable of a single-measurement lowering (the `parity` is stmt 1). -/
def ppmMeasToQStab_readout : QVar := 1

end Compiler.LS
