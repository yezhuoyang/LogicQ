/-
  TypeChecker.Judgment.PPMProgram — AGGREGATOR (M20 strict-folder-ownership refactor).

  Well-formedness of a whole PPM PROGRAM, split by ownership under Judgment/PPMProgram/:
    * `Judgment.PPMProgram.DeadSet`   — `DeadSet` + its ops/lemmas
    * `Judgment.PPMProgram.State`     — `PPMState`/`PPMState.init`/`validLQubit`
    * `Judgment.PPMProgram.Check`     — `checkPPMStmt`/`checkPPMProgram` + site collectors
    * `Judgment.PPMProgram.Soundness` — the meas/targets/dead/use-after-discard theorems
    * `Judgment.PPMProgram.Examples`  — the worked examples

  Every name stays in `namespace TypeChecker`, so `import TypeChecker.Judgment.PPMProgram`
  keeps resolving `PPMState`/`validLQubit`/`checkPPMProgram` + the soundness theorems.
-/
import TypeChecker.Judgment.PPMProgram.DeadSet
import TypeChecker.Judgment.PPMProgram.State
import TypeChecker.Judgment.PPMProgram.Check
import TypeChecker.Judgment.PPMProgram.Soundness
import TypeChecker.Judgment.PPMProgram.Examples
