/-
  TypeChecker.Judgment.PPM.Examples — worked examples for `checkPPM` over a
  TYPED environment.
-/
import TypeChecker.Judgment.PPM.Check

namespace TypeChecker
open ChainQ.GF2

/-! ## Worked examples — over a TYPED environment.

    `q0` is a bare logical qubit; `rep` is the `[[3,1,1]]` repetition code (both
    `Block.valid`, so they enter a `TypedEnv`).  The DRIVING example: a joint
    `Z̄ ⊗ Z̄` measurement across two DIFFERENT codes is REJECTED with no capability,
    and ADMITTED only when an adapter capability supplies a valid merge. -/

def q0 : Block := { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }

def rep : Block :=
  { n := 3,
    stab := [[false, false, false, true,  true,  false],
             [false, false, false, false, true,  true ]],
    lx := [[true,  true,  true,  false, false, false]],
    lz := [[false, false, false, true,  false, false]] }

def tenvQ  : TypedEnv := ⟨[⟨q0, by decide⟩]⟩
def tenvR  : TypedEnv := ⟨[⟨rep, by decide⟩]⟩
def tenvQR : TypedEnv := ⟨[⟨q0, by decide⟩, ⟨rep, by decide⟩]⟩

/-- Joint `Z̄(block 0) ⊗ Z̄(block 1)`. -/
def zzTarget : PPM.MTarget := [(⟨0, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.Z)]

/-- An adapter capability whose connection stabilizer is exactly the joint
    `Z ⊗ Z₀` operator (so the merge measures it). -/
def zzCap : Capability :=
  { kind := .adapterPPM, blocks := [0, 1], ancN := 0,
    connStab := [[false, false, false, false, true, true, false, false]] }

-- single-block logical measurement is native:
example : ok? (checkPPM tenvQ [] [(⟨0, 0⟩, PPM.PLetter.Z)]) = true := by decide
-- a single-block X̄ measurement is ALSO native (X̄ = XXX is a logical operator of `rep`):
example : ok? (checkPPM tenvR [] [(⟨0, 0⟩, PPM.PLetter.X)]) = true := by decide
-- DRIVING EXAMPLE: cross-code joint PPM with NO capability is rejected …
example : ok? (checkPPM tenvQR [] zzTarget) = false := by decide
-- … and ADMITTED only with a valid adapter capability …
example : ok? (checkPPM tenvQR [zzCap] zzTarget) = true := by decide
-- … but a degenerate capability (no connection) fails the merged-code certificate.
example : ok? (checkPPM tenvQR [{ zzCap with connStab := [] }] zzTarget) = false := by decide

-- EMPTY measurement (no factors) is rejected — there is no identity/no-op form:
example : (match checkPPM tenvQ [] [] with | .error .emptyMeasurement => true | _ => false) = true := by decide
-- STRICT QMeas: a >2-factor target is rejected (not a native lattice-surgery observable):
example : (match checkPPM tenvQR [] [(⟨0, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.X)] with
           | .error .nonNativeMeasurement => true | _ => false) = true := by decide
-- a target repeating the SAME logical qubit is rejected (ill-defined joint observable):
example : (match checkPPM tenvQ [] [(⟨0, 0⟩, PPM.PLetter.X), (⟨0, 0⟩, PPM.PLetter.Z)] with
           | .error .nonNativeMeasurement => true | _ => false) = true := by decide

-- ROW SAFETY: an out-of-range logical index is REJECTED (not treated as identity).
example : ok? (checkPPM tenvQ [] [(⟨0, 5⟩, PPM.PLetter.Z)]) = false := by decide
example : (match checkPPM tenvQ [] [(⟨0, 5⟩, PPM.PLetter.Z)] with
           | .error (.badLogicalIndex b i) => b == 0 && i == 5
           | _ => false) = true := by decide

-- RAW ENTRY: a malformed block (zero-width logical) is UNREPRESENTABLE in a
-- TypedEnv; the raw wrapper rejects it at the boundary as `malformedBlock 0`.
def badBlk : Block := { n := 1, stab := [], lx := [[]], lz := [[]] }
example : Block.valid badBlk = false := by decide
example : (match checkPPMFromEnv { blocks := [badBlk] } [] [(⟨0, 0⟩, PPM.PLetter.Z)] with
           | .error (.malformedBlock b) => b == 0 | _ => false) = true := by decide
-- the raw wrapper accepts a good env:
example : ok? (checkPPMFromEnv { blocks := [q0] } [] [(⟨0, 0⟩, PPM.PLetter.Z)]) = true := by decide

end TypeChecker
