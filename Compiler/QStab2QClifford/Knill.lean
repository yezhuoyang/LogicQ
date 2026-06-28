/-
  Compiler.QStab2QClifford.Knill — transversal syndrome extraction, transplanted
  from LeanQEC `QStab/QClifford/Knill.lean` (`qubitGadget`/`knillCircuit`) and the
  `Compile.Calculus` ordered form (`knillSlot`).

  One FRESH ancilla per data qubit, each coupled by a single CNOT, then measured;
  the stabilizer bit is the XOR of ALL the per-qubit raw outcomes (no verifier /
  flag — `syndromeOffsets = range n`).  Because every ancilla touches exactly one
  data qubit there is no hook error — but that fault-tolerance fact lives in
  LeanQEC's Heisenberg layer and is NOT reproved here.

    Z-slot:  Prep0 anc_i;  CNOT data_i anc_i;            Meas anc_i
    X-slot:  H data_i; Prep0 anc_i; CNOT data_i anc_i; H data_i;  Meas anc_i
-/
import Compiler.QStab2QClifford.Scheme

namespace Compiler.QStab2QClifford
open Physical

/-- Knill Z-check plumbing: per data/ancilla pair, `Prep0 anc; CNOT data anc`. -/
def knillZPlumbing (order ancs : List PQubit) : Circuit :=
  (order.zip ancs).flatMap (fun p => [QClifford.Gate.prepZero p.2, QClifford.Gate.CNOT p.1 p.2])

/-- Knill X-check plumbing: H-conjugate the data qubit around the coupling. -/
def knillXPlumbing (order ancs : List PQubit) : Circuit :=
  (order.zip ancs).flatMap
    (fun p => [QClifford.Gate.H p.1, QClifford.Gate.prepZero p.2,
               QClifford.Gate.CNOT p.1 p.2, QClifford.Gate.H p.1])

theorem noMeasParity_knillZPlumbing (order ancs : List PQubit) :
    noMeasParity (knillZPlumbing order ancs) = true := by
  simp [knillZPlumbing, noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

theorem noMeasParity_knillXPlumbing (order ancs : List PQubit) :
    noMeasParity (knillXPlumbing order ancs) = true := by
  simp [knillXPlumbing, noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

end Compiler.QStab2QClifford
