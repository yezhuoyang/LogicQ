/-
  Compiler.QStab2QClifford.Flag — flag syndrome extraction, transplanted from
  LeanQEC `QStab/QClifford/FlagGeneral.lean` (single flag) and `Flag2General.lean`
  (two flags), via the `Compile.Calculus` ordered forms.

    flagX:  one ancilla + one flag.  Two `CNOT anc flag` couplings BRACKET the
            symmetric middle of the data couplings (after `take half`, after
            `drop half`).  Syndrome = anc measurement; flag = separate detector.

    flag2X: one ancilla + two flags.  After EACH data coupling an alternating
            flag coupling (`flag1` on even index, `flag2` on odd).  Scope: data
            weight ≤ 4 (`extractionSpecOk`).  Syndrome = anc; flags = detectors.

  The flag-coupling PLACEMENT (load-bearing for hook detection) is preserved in the
  no-op `plumbing`; only the `measZ`s are grouped.  Hook detection / fault tolerance
  is LeanQEC's Heisenberg-layer result and is NOT reproved here.
-/
import Compiler.QStab2QClifford.Scheme

namespace Compiler.QStab2QClifford
open Physical

/-- Single-flag plumbing: anc `|+⟩`, flag `|0⟩`; data couplings split at the
    midpoint, with a flag coupling after each half; `H` on anc (X-basis read). -/
def flagXPlumbing (order : List PQubit) (anc flag : PQubit) : Circuit :=
  [QClifford.Gate.prepPlus anc, QClifford.Gate.prepZero flag] ++
    (order.take (order.length / 2)).map (fun q => QClifford.Gate.CNOT anc q) ++
    [QClifford.Gate.CNOT anc flag] ++
    (order.drop (order.length / 2)).map (fun q => QClifford.Gate.CNOT anc q) ++
    [QClifford.Gate.CNOT anc flag, QClifford.Gate.H anc]

/-- The interleaved data/flag coupling chain (index `i` alternates the flag). -/
def flag2Chain (anc flag1 flag2 : PQubit) : Nat → List PQubit → Circuit
  | _, [] => []
  | i, q :: qs =>
      [QClifford.Gate.CNOT anc q,
       if i % 2 = 0 then QClifford.Gate.CNOT anc flag1 else QClifford.Gate.CNOT anc flag2] ++
        flag2Chain anc flag1 flag2 (i + 1) qs

/-- Two-flag plumbing: anc `|+⟩`, flags `|0⟩`; the interleaved chain; `H` on anc. -/
def flag2XPlumbing (order : List PQubit) (anc flag1 flag2 : PQubit) : Circuit :=
  [QClifford.Gate.prepPlus anc, QClifford.Gate.prepZero flag1, QClifford.Gate.prepZero flag2] ++
    flag2Chain anc flag1 flag2 0 order ++ [QClifford.Gate.H anc]

theorem noMeasParity_flagXPlumbing (order : List PQubit) (anc flag : PQubit) :
    noMeasParity (flagXPlumbing order anc flag) = true := by
  simp only [flagXPlumbing, noMeasParity_append, noMeasParity_cnotFrom, Bool.and_true]
  simp [noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

theorem noMeasParity_flag2Chain (anc flag1 flag2 : PQubit) (i : Nat) (qs : List PQubit) :
    noMeasParity (flag2Chain anc flag1 flag2 i qs) = true := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih =>
      simp only [flag2Chain, noMeasParity_append, ih (i + 1), Bool.and_true]
      split <;> simp [noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

theorem noMeasParity_flag2XPlumbing (order : List PQubit) (anc flag1 flag2 : PQubit) :
    noMeasParity (flag2XPlumbing order anc flag1 flag2) = true := by
  simp only [flag2XPlumbing, noMeasParity_append, noMeasParity_flag2Chain, Bool.and_true]
  simp [noMeasParity, QClifford.Gate.isMeas, QClifford.Gate.isClassical]

end Compiler.QStab2QClifford
