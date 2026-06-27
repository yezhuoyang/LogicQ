/-
  TypeChecker.Judgment.PPM — AGGREGATOR (M20 strict-folder-ownership refactor).

  The cross-code PPM capability matcher, split by ownership under Judgment/PPM/:
    * `Judgment.PPM.Lift`        — GF(2)/symplectic lifting helpers + the named
                                   certificate builders (`liftedStabOf`/`mergedStabOf`/`targetPOf`)
    * `Judgment.PPM.Certificate` — the `TypedPPM` evidence structure
    * `Judgment.PPM.Check`       — `ppmObligations` / `checkPPM` / `checkPPMFromEnv`
    * `Judgment.PPM.Examples`    — the worked examples + the shared env fixtures
                                   (`q0`/`tenvQ`/`tenvR`/`tenvQR`/`zzTarget`/`zzCap`)

  Every name stays in `namespace TypeChecker`, so `import TypeChecker.Judgment.PPM`
  keeps resolving `checkPPM`/`TypedPPM` AND the fixtures unchanged.
-/
import TypeChecker.Judgment.PPM.Lift
import TypeChecker.Judgment.PPM.Certificate
import TypeChecker.Judgment.PPM.Check
import TypeChecker.Judgment.PPM.Examples
