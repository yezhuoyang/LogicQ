/-
  Compiler.Demo.Direct — the direct fragment of the demo pipeline (§1):
  the FULL pipeline, exact source = emitted, for `H ; S ; H`.
-/
import Compiler.Demo.Common

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## §1. The direct fragment — the FULL pipeline, exact source = emitted. -/

/-- A source program: `H ; S ; H` on the single logical qubit of `tenvQ`. -/
def srcHSH : List LogicalOp := [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩, .hGate ⟨0, 0⟩]

-- `compile?` source-checks then lowers `srcHSH`; the emitted Mixed IR TYPE-CHECKS,
-- is three DIRECT transversals, and the simulator run of the EMITTED program EQUALS
-- the source circuit (exact, direct fragment) — the expected `H S H |0⟩` state.
example : (match compile? .executable demoCfg tenvQ srcHSH with
           | .ok c => ok? (checkLogicalExec [] tenvQ c.prog) | _ => false) = true := by decide
example : (match compile? .executable demoCfg tenvQ srcHSH with
           | .ok c => (loweredGates (Layout.flat 4) c.prog).length == 3 | _ => false) = true := by decide
example : (match compile? .executable demoCfg tenvQ srcHSH with
           | .ok c => decide (runGates 1 (loweredGates (Layout.flat 4) c.prog) (init 1)
                              = runGates 1 (sourceGates (Layout.flat 4) srcHSH) (init 1))
           | .error _ => false) = true := by decide
example : runGates 1 (sourceGates (Layout.flat 4) srcHSH) (init 1) = ([⟨1, 1⟩, ⟨1, -1⟩] : State) := by decide

-- `compile?` REJECTS a malformed source program (bad logical index) — `compile?_sourceOk`.
example : ok? (compile? .executable demoCfg tenvQ [.hGate ⟨0, 99⟩]) = false := by decide

end Compiler.Demo
