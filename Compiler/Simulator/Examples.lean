/-
  Compiler.Simulator.Examples — the §5 algorithm-outcome tests, the §6
  source-vs-EMITTED comparison tests, and the §7 PPM-channel example, split out of
  Compiler/Simulator.lean.
-/
import Compiler.Simulator.Algorithms
import Compiler.Simulator.ExecMixed

namespace Compiler.Sim
open Compiler TypeChecker PPM ChainQ.GF2 Logical

-- Deutsch–Jozsa: constant ⇒ query measured 0 with certainty (never 1)…
example : regProb 2 [0] [true]  (runGates 2 djConstant (init 2)) = 0 := by decide
-- …balanced ⇒ query measured 1 with certainty (never 0).
example : regProb 2 [0] [false] (runGates 2 djBalanced (init 2)) = 0 := by decide
-- and the two distributions genuinely DIFFER (so the simulator is not vacuous):
example : runGates 2 djConstant (init 2) ≠ runGates 2 djBalanced (init 2) := by decide

-- Grover: the marked item |11⟩ is found with certainty (both qubits measure 1).
example : regProb 2 [0] [false] (runGates 2 grover2 (init 2)) = 0 := by decide
example : regProb 2 [1] [false] (runGates 2 grover2 (init 2)) = 0 := by decide

-- Simon (s = 11): the measured input is uniform over {00, 11}; 01 and 10 never occur.
example : regProb 4 [0, 1] [true, false] (runGates 4 simon2 (init 4)) = 0 := by decide
example : regProb 4 [0, 1] [false, true] (runGates 4 simon2 (init 4)) = 0 := by decide
-- …while the orthogonal outcomes DO occur (nonzero weight), confirming the spread.
example : regProb 4 [0, 1] [false, false] (runGates 4 simon2 (init 4)) ≠ 0 := by decide
example : regProb 4 [0, 1] [true, true]   (runGates 4 simon2 (init 4)) ≠ 0 := by decide

/-! ### §6 tests. -/

-- LAYOUT (1C): same block, DIFFERENT logical index ⇒ DIFFERENT sim qubits.  A
-- block-id-only layout would (wrongly) collapse ⟨0,0⟩ and ⟨0,1⟩ onto qubit 0.
example : sourceGates (Layout.flat 4) [.cnotGate ⟨0, 0⟩ ⟨0, 1⟩] = [Gate.CNOT 0 1] := by decide
example : sourceGates (Layout.flat 4) [.hGate ⟨0, 0⟩] ≠ sourceGates (Layout.flat 4) [.hGate ⟨0, 1⟩] := by decide

-- SOURCE vs EMITTED (Task 6): compile `H;S;H` to a proof-carrying mixed program,
-- DECODE the EMITTED transversals, and check the decoded circuit's distribution
-- equals the source circuit's — running the emitted instructions, not source ops.
example : (match compile? .executable { caps := [], anc := ⟨1, 0⟩ } tenvQ hshProg with
           | .ok c => decide (runGates 1 (loweredGates (Layout.flat 4) c.prog) (init 1)
                              = runGates 1 (sourceGates (Layout.flat 4) hshProg) (init 1))
           | .error _ => false) = true := by decide
-- and that common distribution is the expected H S H |0⟩ state.
example : runGates 1 (sourceGates (Layout.flat 4) hshProg) (init 1) = ([⟨1, 1⟩, ⟨1, -1⟩] : State) := by decide
-- the emitted program really is the two direct transversals + one (NOT a PPM gadget):
example : (match compile? .executable { caps := [], anc := ⟨1, 0⟩ } tenvQ hshProg with
           | .ok c => (loweredGates (Layout.flat 4) c.prog).length == 3 | _ => false) = true := by decide

-- (M13 task 2) BLOCK-LEVEL syntax decodes honestly: a `blockTransversal 0 H` source
-- op is the H on the block's qubit, and compiles+emits a transversal the sim decodes
-- to the SAME gate — source and emitted distributions agree on the direct fragment.
example : sourceGates (Layout.flat 4) [.blockTransversal 0 hGate2x2] = [Gate.H 0] := by decide
example : (match compile? .executable { caps := [], anc := ⟨1, 0⟩ } tenvQ [.blockTransversal 0 hGate2x2] with
           | .ok c => decide (runGates 1 (loweredGates (Layout.flat 4) c.prog) (init 1)
                              = runGates 1 (sourceGates (Layout.flat 4) [.blockTransversal 0 hGate2x2]) (init 1))
           | .error _ => false) = true := by decide

/-! ## §7. Measurement with an explicit classical outcome (PPM channel).

    The Mixed `Step.ppm` rule delegates to `PPM.Steps`; a logical measurement binds
    its `±1` outcome into the classical store.  This is carrier-PARAMETRIC (the
    classical/frame evolution is independent of the quantum back-end `Q`), so it
    holds for the simulator's `State` carrier too.  (The quantum back-action
    `proj` is the deferred part; here we exhibit the OUTCOME threading.) -/

-- Measuring logical `Z` on ⟨0,0⟩ binds outcome `r ↦ +1` in the store (here `+1`;
-- the `-1` branch is symmetric) — a real `PPM.Steps` run reaching `skip`.
example (I : PPM.QInterp State) (ρ : State) :
    ∃ ρ' F', PPM.Steps I ⟨ρ, PPM.Store.empty, PPM.Frame.id0,
              .meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)] ;; .skip⟩
              [.out .pos, .tau]
              ⟨ρ', (PPM.Store.empty).set 0 .pos, F', .skip⟩ :=
  ⟨_, _, PPM.red_meas I 0 _ .pos .skip⟩

end Compiler.Sim
