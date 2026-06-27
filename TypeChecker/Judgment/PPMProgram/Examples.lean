/-
  TypeChecker.Judgment.PPMProgram.Examples — tests for the PPM program checker
  over the bare-qubit env `tenvQ`.
-/
import TypeChecker.Judgment.PPMProgram.Check

namespace TypeChecker
open ChainQ.GF2 Logical PPM

/-! ## Tests (over the bare-qubit env `tenvQ`, block 0 with one logical qubit). -/

example : ok? (checkPPMProgram tenvQ []
    (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)] ;; .frame ⟨0, 0⟩ .X ;; .discard ⟨0, 0⟩)) = true := by decide
example : ok? (checkPPMProgram tenvQ []
    (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)] ;; .ite 0 .skip .skip)) = true := by decide

-- REJECTIONS:
example : (match checkPPMProgram tenvQ [] (.ite 0 .skip .skip) with
           | .error (.unboundOutcome r) => r == 0 | _ => false) = true := by decide
example : (match checkPPMProgram tenvQ [] (.frame ⟨0, 5⟩ .X) with
           | .error (.badLogicalIndex b i) => b == 0 && i == 5 | _ => false) = true := by decide
example : ok? (checkPPMProgram ⟨[⟨{ q0 with live := false }, by decide⟩]⟩ [] (.frame ⟨0, 0⟩ .X)) = false := by decide
example : (match checkPPMProgram tenvQ [] (.meas 0 []) with
           | .error .emptyMeasurement => true | _ => false) = true := by decide
example : ok? (checkPPMProgram tenvQR []
    (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.X)])) = false := by decide

-- RESOURCE HOLE (the M9 fix): use-after-discard is rejected.
example : (match checkPPMProgram tenvQ [] (.discard ⟨0, 0⟩ ;; .frame ⟨0, 0⟩ .X) with
           | .error (.useAfterDiscard b i) => b == 0 && i == 0 | _ => false) = true := by decide
example : ok? (checkPPMProgram tenvQ [] (.discard ⟨0, 0⟩ ;; .discard ⟨0, 0⟩)) = false := by decide   -- double-discard
example : ok? (checkPPMProgram tenvQ [] (.discard ⟨0, 0⟩ ;; .meas 1 [(⟨0, 0⟩, PPM.PLetter.Z)])) = false := by decide  -- measure after discard

-- DeadSet SEMANTICS (M10), discriminating tests:
-- ite branch UNION: discarding ⟨0,0⟩ in ONE branch marks it dead afterward, so a
-- following frame is rejected (would be ACCEPTED under intersection/empty-join):
example : (match checkPPMProgram tenvQ []
    (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)] ;; .ite 0 (.discard ⟨0, 0⟩) .skip ;; .frame ⟨0, 0⟩ .X) with
    | .error (.useAfterDiscard _ _) => true | _ => false) = true := by decide
-- loop "discards nothing" via SUBSET: a loop body that discards is rejected:
example : ok? (checkPPMProgram tenvQ [] (.forLoop 3 (.discard ⟨0, 0⟩))) = false := by decide
-- …while a loop body that discards nothing is accepted:
example : ok? (checkPPMProgram tenvQ [] (.forLoop 3 (.frame ⟨0, 0⟩ .X))) = true := by decide

end TypeChecker
