/-
  Compiler.Demo.Algorithms — the textbook algorithms as `LogicalOp` source programs
  (§2 decode), their ideal validated outcomes (§3), and the well-formed-vs-compilable
  distinction (§4).
-/
import Compiler.Demo.Common

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## §2. The algorithms as `LogicalOp` programs (one source AST).

    Logical qubit `⟨i,0⟩` = simulator qubit `i` (the `flat 1` layout); each algorithm
    qubit is its own single-logical block.  `X`/`Z` are frame ops, `H` direct, and
    `CNOT`/`CZ` lower to (ideal-assumed) gadgets. -/

/-- Deutsch–Jozsa (constant `f`) — uses only `X` (frame) + `H` (direct). -/
def djConstantSrc : List LogicalOp :=
  [.xGate ⟨1, 0⟩, .hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩, .hGate ⟨0, 0⟩]
/-- Deutsch–Jozsa (balanced `f(x)=x`) — oracle is `CNOT query→ancilla`. -/
def djBalancedSrc : List LogicalOp :=
  [.xGate ⟨1, 0⟩, .hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩, .cnotGate ⟨0, 0⟩ ⟨1, 0⟩, .hGate ⟨0, 0⟩]
/-- 2-qubit Grover (marked `|11⟩`): `CZ` oracle + diffusion. -/
def grover2Src : List LogicalOp :=
  [.hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩, .czGate ⟨0, 0⟩ ⟨1, 0⟩, .hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩,
   .xGate ⟨0, 0⟩, .xGate ⟨1, 0⟩, .czGate ⟨0, 0⟩ ⟨1, 0⟩, .xGate ⟨0, 0⟩, .xGate ⟨1, 0⟩,
   .hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩]
/-- Simon (n=2, secret `s=11`): inputs `⟨0,0⟩ ⟨1,0⟩`, outputs `⟨2,0⟩ ⟨3,0⟩`. -/
def simon2Src : List LogicalOp :=
  [.hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩,
   .cnotGate ⟨0, 0⟩ ⟨2, 0⟩, .cnotGate ⟨1, 0⟩ ⟨2, 0⟩,
   .cnotGate ⟨0, 0⟩ ⟨3, 0⟩, .cnotGate ⟨1, 0⟩ ⟨3, 0⟩,
   .hGate ⟨0, 0⟩, .hGate ⟨1, 0⟩]

-- The source AST decodes (via the SAME `opGate?` the simulator uses) to the textbook
-- circuits — there is no separate "simulator language":
example : sourceGates (Layout.flat 1) djConstantSrc = djConstant := by decide
example : sourceGates (Layout.flat 1) djBalancedSrc = djBalanced := by decide
example : sourceGates (Layout.flat 1) grover2Src    = grover2    := by decide
example : sourceGates (Layout.flat 1) simon2Src     = simon2     := by decide

/-! ## §3. Ideal semantics of the SOURCE programs (validated outcomes). -/

-- Deutsch–Jozsa: constant ⇒ query (qubit 0) measures 0 with certainty; balanced ⇒ 1.
example : regProb 2 [0] [true]  (runGates 2 (sourceGates (Layout.flat 1) djConstantSrc) (init 2)) = 0 := by decide
example : regProb 2 [0] [false] (runGates 2 (sourceGates (Layout.flat 1) djBalancedSrc) (init 2)) = 0 := by decide
-- 2-qubit Grover: finds `|11⟩` with certainty (both qubits measure 1).
example : regProb 2 [0] [false] (runGates 2 (sourceGates (Layout.flat 1) grover2Src) (init 2)) = 0 := by decide
example : regProb 2 [1] [false] (runGates 2 (sourceGates (Layout.flat 1) grover2Src) (init 2)) = 0 := by decide
-- Simon: measured input is uniform over {00, 11}; 01 / 10 never occur.
example : regProb 4 [0, 1] [true, false] (runGates 4 (sourceGates (Layout.flat 1) simon2Src) (init 4)) = 0 := by decide
example : regProb 4 [0, 1] [false, true] (runGates 4 (sourceGates (Layout.flat 1) simon2Src) (init 4)) = 0 := by decide
example : regProb 4 [0, 1] [true, true]  (runGates 4 (sourceGates (Layout.flat 1) simon2Src) (init 4)) ≠ 0 := by decide

/-! ## §4. compile? COMPILES the gadget-free fragment; `sourceCompilable` rejects
    well-formed-but-unavailable implementations. -/

-- DJ-CONSTANT fully compiles: `X` → frame, `H` → direct transversal (k=1 blocks).
example : ok? (compile? .executable dj2Cfg tenv2 djConstantSrc) = true := by decide
-- and the emitted program TYPE-CHECKS:
example : (match compile? .executable dj2Cfg tenv2 djConstantSrc with
           | .ok c => ok? (checkLogicalExec [] tenv2 c.prog) | _ => false) = true := by decide

-- THE WELL-FORMED vs COMPILABLE DISTINCTION (M16 task 2):
-- `djBalancedSrc` is operand-WELL-FORMED …
example : sourceWellFormed [] tenv2 PPMState.init djBalancedSrc = true := by decide
-- … but NOT COMPILABLE on a plain env: its `CNOT` needs a cross-block adapter
-- capability that is unavailable, so `compile?` rejects it.
example : sourceCompilable .executable dj2Cfg tenv2 djBalancedSrc = false := by decide
example : ok? (compile? .executable dj2Cfg tenv2 djBalancedSrc) = false := by decide
-- likewise Grover (`CZ`) and Simon (`CNOT`) are well-formed but not compilable here:
example : sourceWellFormed [] tenv2 PPMState.init grover2Src = true := by decide
example : sourceCompilable .executable dj2Cfg tenv2 grover2Src = false := by decide
example : sourceCompilable .executable { caps := [], anc := ⟨4, 0⟩ } tenv4 simon2Src = false := by decide

end Compiler.Demo
