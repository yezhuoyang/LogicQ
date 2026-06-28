/-
  Compiler.QStab2QClifford.Standard — the DIRECT single-measurement schemes
  (transplanted from LeanQEC `Standard.xCircuit`/`zCircuit`, plus the LogicQ-local
  destructive one-qubit readouts).  Each binds its syndrome by ONE measurement
  straight into the result var — no auxiliary bits, no parity gate.

    standardX:    Prep+ anc; CNOT anc q…; H anc; Meas anc → v
    standardZ:    Prep0 anc; CNOT q anc…;        Meas anc → v
    destructiveX: H q;  Meas q → v
    destructiveZ:        Meas q → v
-/
import Compiler.QStab2QClifford.Scheme

namespace Compiler.QStab2QClifford

open Physical

/-- The non-measurement prefix of a direct gadget. -/
def directPrefix : ExtractionSpec → Circuit
  | .standardX order anc =>
      [QClifford.Gate.prepPlus anc] ++ order.map (fun q => QClifford.Gate.CNOT anc q) ++
        [QClifford.Gate.H anc]
  | .standardZ order anc =>
      [QClifford.Gate.prepZero anc] ++ order.map (fun q => QClifford.Gate.CNOT q anc)
  | .destructiveX q => [QClifford.Gate.H q]
  | _ => []   -- destructiveZ and the multi-measurement schemes

/-- The single qubit a direct gadget measures. -/
def directMeasQubit : ExtractionSpec → PQubit
  | .standardX _ anc | .standardZ _ anc => anc
  | .destructiveX q | .destructiveZ q => q
  | _ => 0

theorem noMeasParity_directPrefix (spec : ExtractionSpec) :
    noMeasParity (directPrefix spec) = true := by
  cases spec <;>
    simp [directPrefix, noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

/-- A direct gadget consumes one trace slot and writes its outcome into `v`. -/
theorem traceFold_directProp (outcome : Nat → Bool) (spec : ExtractionSpec) (v k : Nat) (σ : Store) :
    traceFold outcome (directPrefix spec ++ [QClifford.Gate.meas (directMeasQubit spec) v]) k σ
      = (k + 1, σ.set v (outcome k)) := by
  rw [traceFold_append, traceFold_noop outcome (directPrefix spec) (noMeasParity_directPrefix spec)]
  simp [traceFold]

end Compiler.QStab2QClifford
