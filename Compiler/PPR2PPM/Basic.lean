/-
  Compiler.LogicalToPPM — PPM-FRAGMENT evidence.

  DESIGN SHIFT (M9): the original M8 PPM-only compiler (a `LogicalOp` list lowered
  ENTIRELY to PPM) is SUPERSEDED by `Compiler.Mixed`, where PPM is one checked
  target sublanguage among transversal gates, logical automorphisms, and code
  switches.  What remains here is the proof-carrying evidence for a single PPM
  FRAGMENT: a `PPM.Stmt` together with a proof it passes `checkPPMProgram`.
-/
import TypeChecker.Basic

namespace Compiler
open TypeChecker PPM

/-- A PPM program FRAGMENT carrying the proof that it type-checks. -/
structure CompiledPPM (Γ : TypedEnv) (caps : List Capability) where
  stmt  : PPM.Stmt
  typed : ok? (checkPPMProgram Γ caps stmt) = true

/-- Validate a raw PPM fragment into proof-carrying evidence. -/
def mkCompiledPPM? (Γ : TypedEnv) (caps : List Capability) (s : PPM.Stmt) :
    Except TypeError (CompiledPPM Γ caps) :=
  if h : ok? (checkPPMProgram Γ caps s) = true then .ok ⟨s, h⟩
  else .error (.other "PPM fragment does not type-check under the environment")

/-! ## Soundness (∀-theorems, separate from the `decide` examples). -/

/-- A compiled fragment is WELL-FORMED: it passes `checkPPMProgram`. -/
theorem CompiledPPM.wellFormed {Γ : TypedEnv} {caps : List Capability}
    (c : CompiledPPM Γ caps) : ok? (checkPPMProgram Γ caps c.stmt) = true := c.typed

/-- Every measurement emitted by a compiled fragment is LEGAL under the
    TypeChecker (via the structural `checkPPMStmt_meas_sound`). -/
theorem CompiledPPM.meas_legal {Γ : TypedEnv} {caps : List Capability}
    (c : CompiledPPM Γ caps) :
    (measTargets c.stmt).all (fun P => ok? (checkPPM Γ caps P)) = true := by
  have hwf := c.typed
  unfold checkPPMProgram at hwf
  cases hc : checkPPMStmt Γ caps PPMState.init c.stmt with
  | error e => rw [hc] at hwf; simp [ok?] at hwf
  | ok b    => exact checkPPMStmt_meas_sound Γ caps c.stmt PPMState.init b hc

/-- Every `frame`/`discard` of a compiled fragment targets a valid logical qubit. -/
theorem CompiledPPM.targets_valid {Γ : TypedEnv} {caps : List Capability}
    (c : CompiledPPM Γ caps) :
    (frameDiscardTargets c.stmt).all (validLQubit Γ) = true := by
  have hwf := c.typed
  unfold checkPPMProgram at hwf
  cases hc : checkPPMStmt Γ caps PPMState.init c.stmt with
  | error e => rw [hc] at hwf; simp [ok?] at hwf
  | ok b    => exact checkPPMStmt_targets_valid Γ caps c.stmt PPMState.init b hc

/-! ## Tests. -/

-- a native single-qubit measurement fragment validates into evidence:
example : ok? (mkCompiledPPM? tenvQ [] (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)])) = true := by decide
-- an empty / non-native measurement fragment is rejected:
example : ok? (mkCompiledPPM? tenvQ [] (.meas 0 [])) = false := by decide

end Compiler
