/-
  Compiler.LS.PPM — the PPM → LS adapter.

  A logical PPM measurement does NOT lower to a physical LS measurement automatically:
  the logical→physical realisation of the measured operator is exactly the surgery
  certificate the LS layer demands.  So a `PPM.Stmt.meas` lowers to an `LS.meas` ONLY
  when supplied an explicit PHYSICAL Pauli witness (optionally with a `SurgeryCert`);
  without one it is NOT lowerable (`noPhysicalWitness`).  The PPM 1-or-2-body native
  discipline (`PPM.MTarget.wf`) is preserved.

  This does NOT claim the logical↔physical map is correct — the witness/cert IS the
  recorded (and partly deferred) evidence.  Mathlib-free.
-/
import Compiler.LS.LowerQStab
import PPM.Syntax

namespace Compiler.LS
open QStab Physical Logical

/-- The PPM NATIVE surgery discipline: a logical Pauli product over 1 or 2 distinct
    logical qubits (reusing `PPM.MTarget.wf`). -/
def ppmNative (P : PPM.MTarget) : Bool := PPM.MTarget.wf P

/-- Lower ONE PPM logical Pauli measurement to an LS measurement op — ONLY with an
    explicit PHYSICAL witness `w` (the surgery's physical realisation of the logical
    operator).  No witness ⇒ NOT lowerable.  Keeps the 1-or-2-body discipline. -/
def ppmMeasToLS? (sched : Option Sched) (P : PPM.MTarget) (witness? : Option SPauli) :
    Except LSError LSOp :=
  if !ppmNative P then .error (.ppmNotNative P.length)
  else match witness? with
    | none   => .error .noPhysicalWitness
    | some w =>
        if !w.wfMeas then .error (.identityFactor w)   -- the physical witness must be a valid measurement
        else .ok (.meas sched w)

/-- Lower a PPM measurement to LS using a `SurgeryCert` as the witness source, with the
    witness CONNECTED to the certificate.  Requires: the `cert` passes its structural
    `check`; the `witness` is a wf measurement, in range for the `numQubits`-qubit
    patch; and — crucially — the witness DENSIFIES to exactly the cert's measured parity
    (`SPauli.toDense numQubits witness = cert.measuredParity`) and that parity spans the
    whole patch (`cert.measuredParity.length = numQubits`).  So the physical witness can
    no longer be an arbitrary Pauli unrelated to the certificate. -/
def ppmMeasToLSWithCert? (numQubits : Nat) (sched : Option Sched) (P : PPM.MTarget)
    (cert : SurgeryCert) (witness : SPauli) : Except LSError LSOp :=
  if !cert.check then .error (.other "surgery certificate failed its structural check")
  else if !witness.wfMeas then .error (.identityFactor witness)
  else if !witness.inRange numQubits then .error (.sparseOutOfRange witness numQubits)
  else if !decide (cert.measuredParity.length = numQubits) then
    .error (.certWitnessMismatch witness cert.measuredParity)
  else if !decide (SPauli.toDense numQubits witness = cert.measuredParity) then
    .error (.certWitnessMismatch witness cert.measuredParity)
  else ppmMeasToLS? sched P (some witness)

/-- Lower a PPM measurement ALL THE WAY to QStab (PPM → LS → QStab): build a tiny LS
    program that measures the witness and reads it out as a parity, then `lowerChecked`. -/
def ppmToQStab? (numQubits : Nat) (sched : Option Sched) (P : PPM.MTarget)
    (witness? : Option SPauli) : Except LSError QStab.StabilizerProg := do
  let op ← ppmMeasToLS? sched P witness?
  let prog : Program := { numQubits := numQubits, ops := [op, .parity [0]] }
  let (qstab, _) ← lowerChecked prog
  return qstab

/-! ## §1. Checked examples. -/

/-- A 2-body logical `ZZ` measurement (native PPM). -/
def ppmZZ : PPM.MTarget := [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z)]
/-- A 3-body logical measurement (NOT native — violates the 1-or-2-body discipline). -/
def ppm3 : PPM.MTarget := [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z), (⟨2, 0⟩, .Z)]
/-- A physical witness: the 2-physical-qubit `ZZ` parity realising the logical `ZZ`. -/
def witnessZZ : SPauli := [(0, .Z), (1, .Z)]

-- WITHOUT a physical witness, a logical measurement is NOT lowerable:
example : (ppmMeasToLS? none ppmZZ none).toOption.isSome = false := by decide
-- WITH a witness, it lowers to an LS measurement op:
example : (ppmMeasToLS? none ppmZZ (some witnessZZ)).toOption.isSome = true := by decide
-- the 1-or-2-body discipline is kept: a 3-body PPM measurement is rejected:
example : (ppmMeasToLS? none ppm3 (some [(0, .Z), (1, .Z), (2, .Z)])).toOption.isSome = false := by decide
-- a witness that is not a valid measurement (identity factor) is rejected:
example : (ppmMeasToLS? none ppmZZ (some [(0, .I)])).toOption.isSome = false := by decide

-- end-to-end: PPM (with witness) → LS → a WELL-FORMED QStab program; without a witness, none:
example : (ppmToQStab? 2 (some ⟨0, 0⟩) ppmZZ (some witnessZZ)).toOption.map (·.wf) = some true := by decide
example : (ppmToQStab? 2 (some ⟨0, 0⟩) ppmZZ none).toOption.isSome = false := by decide
-- …and the witness `ZZ` became the physical `prop` measurement + its readout parity:
example : (ppmToQStab? 2 (some ⟨0, 0⟩) ppmZZ (some witnessZZ)).toOption.map (·.dataflow)
    = some [ .prop (some ⟨0, 0⟩) (ofString "ZZ"), .parity [0] ] := by decide

-- a `SurgeryCert`-gated lowering (using the migrated `LS.SurgeryCert`): an honest cert
-- (all fault obligations deferred) lowers; a cert dishonestly marking distance
-- CERTIFIED fails its `check` and does not lower.
def certZZ' : SurgeryCert where
  measuredParity        := ofString "ZZ"
  preservedLogicals     := [ofString "XX"]
  byproductFrame        := []
  claimedMergedCommutes := true
  claimedDetectorsDet   := true
  claimedIrreducible    := true
  faults                := {}

-- a MATCHING cert/witness (witness densifies to the cert's measured `ZZ` parity) is accepted:
example : (ppmMeasToLSWithCert? 2 none ppmZZ certZZ' witnessZZ).toOption.isSome = true := by decide
-- a MISMATCHED witness (`XX` ≠ the cert's `ZZ` parity) is REJECTED:
example : (ppmMeasToLSWithCert? 2 none ppmZZ certZZ' [(0, .X), (1, .X)]).toOption.isSome = false := by decide
-- an OUT-OF-RANGE witness (qubit 5 ≥ numQubits = 2) is REJECTED:
example : (ppmMeasToLSWithCert? 2 none ppmZZ certZZ' [(0, .Z), (5, .Z)]).toOption.isSome = false := by decide
-- a wrong-LENGTH cert (`ZZ` parity but numQubits = 3) is REJECTED:
example : (ppmMeasToLSWithCert? 3 none ppmZZ certZZ' witnessZZ).toOption.isSome = false := by decide
-- a DISHONEST cert (distance marked CERTIFIED) fails its `check` and does not lower:
example : (ppmMeasToLSWithCert? 2 none ppmZZ { certZZ' with faults := { distance := .certified } } witnessZZ).toOption.isSome = false := by decide

end Compiler.LS
