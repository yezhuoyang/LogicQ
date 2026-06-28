/-
  Compiler.Demo.Frames — the real operational semantics of compiled programs (§5),
  the exact-operational fragment classification (§5b), and negative source
  well-formedness (§6).
-/
import Compiler.Demo.Algorithms

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## §5. REAL OPERATIONAL semantics of compiled programs (M18 task 1+2).

    `xGate`/`zGate` now lower to a real `MixedInstr.pauli` whose `Step.pauli` rule
    APPLIES the Pauli to the carrier (M17 lowered them to a record-only `.ppm (.frame)`,
    whose `Step` left the carrier UNCHANGED — the gap this milestone closes).  We RUN
    each EMITTED program through `execMixed` — an executable interpreter whose `.pauli`
    step is PROVEN equal to the `Step.pauli` carrier update (`step_pauli_matches_exec`)
    and whose `.transversal` applies the symplectic Clifford at the block's qubit
    (layout-aware) — and compare to the ideal source circuit.  This does NOT rely on the
    `loweredGates` decoder; `execMixed` returns `none` (stuck) on anything it cannot
    actually run, rather than silently dropping it. -/

def xhSrc : List LogicalOp := [.xGate ⟨0, 0⟩, .hGate ⟨0, 0⟩]
def zhSrc : List LogicalOp := [.zGate ⟨0, 0⟩, .hGate ⟨0, 0⟩]
def xsSrc : List LogicalOp := [.xGate ⟨0, 0⟩, .sGate ⟨0, 0⟩]

-- `X;H`: RUN the emitted program operationally (the `.pauli` is APPLIED, then `H`),
-- giving the same state as the ideal source `H X |0⟩ = |−⟩` (unnormalised `[1,-1]`).
example : (match compile? .executable demoCfg tenvQ xhSrc with
           | .ok c => decide (execMixed (Layout.flat 4) 1 c.prog (init 1)
                              = some (runGates 1 (sourceGates (Layout.flat 4) xhSrc) (init 1)))
           | .error _ => false) = true := by decide
example : runGates 1 (sourceGates (Layout.flat 4) xhSrc) (init 1) = ([⟨1, 0⟩, ⟨-1, 0⟩] : State) := by decide
-- `Z;H` and `X;S`: emitted RUN equals the ideal source run.
example : (match compile? .executable demoCfg tenvQ zhSrc with
           | .ok c => decide (execMixed (Layout.flat 4) 1 c.prog (init 1)
                              = some (runGates 1 (sourceGates (Layout.flat 4) zhSrc) (init 1)))
           | .error _ => false) = true := by decide
example : (match compile? .executable demoCfg tenvQ xsSrc with
           | .ok c => decide (execMixed (Layout.flat 4) 1 c.prog (init 1)
                              = some (runGates 1 (sourceGates (Layout.flat 4) xsSrc) (init 1)))
           | .error _ => false) = true := by decide
-- DJ-CONSTANT: the emitted program (a `.pauli` + three `.transversal`s) RUN operationally
-- equals the ideal source run.
example : (match compile? .executable dj2Cfg tenv2 djConstantSrc with
           | .ok c => decide (execMixed (Layout.flat 1) 2 c.prog (init 2)
                              = some (runGates 2 (sourceGates (Layout.flat 1) djConstantSrc) (init 2)))
           | .error _ => false) = true := by decide

-- HONESTY: `execMixed` does NOT silently drop — it gets STUCK (`none`) on an
-- instruction it cannot run (a magic obligation / PPM gadget), unlike the
-- `loweredGates` decoder which `filterMap`s it away to a SHORTER list.
example : execMixed (Layout.flat 4) 1 [MixedInstr.magic { kind := .tGate, target := ⟨0, 0⟩ }] (init 1) = none := by decide
example : loweredGates (Layout.flat 4) [MixedInstr.magic { kind := .tGate, target := ⟨0, 0⟩ }] = [] := by decide
example : execMixed (Layout.flat 4) 1 [MixedInstr.ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)])] (init 1) = none := by decide

-- the simulator's gate algebra is correct: `X;H ≡ H;Z` and `Z;H ≡ H;X` (Clifford
-- conjugation `HXH = Z`, `HZH = X`) — the reason a logical Pauli is a legitimate
-- exact-supported operation.
example : runGates 1 [Gate.X 0, Gate.H 0] (init 1) = runGates 1 [Gate.H 0, Gate.Z 0] (init 1) := by decide
example : runGates 1 [Gate.Z 0, Gate.H 0] (init 1) = runGates 1 [Gate.H 0, Gate.X 0] (init 1) := by decide

/-! ## §5b. The EXACT-operational fragment (M18 task 3).

    A precise classification of which source ops have EXACT operational semantics
    (run by `execMixed`/`Step` and matched to the ideal simulator, §5 above) versus
    those that are only typechecked / ideal / deferred. -/

/-- `true` iff the op has EXACT operational semantics: logical Paulis
    (`xGate`/`zGate` → APPLIED `.pauli`) and direct Cliffords (`hGate`/`sGate` on a
    `k=1` block, `blockTransversal` H/S → `.transversal`, the exact symplectic action).
    NOT exact: `measure` (typechecked; ideal projective readout), `cnotGate`/`czGate`
    (typechecked lowerings to PPM gadgets under an IDEAL gadget-channel assumption;
    `czGate` rides the PLACEHOLDER `progCZAt` and is EXPERIMENTAL), `tGate` (deferred
    magic obligation). -/
def exactSupportedOp : LogicalOp → Bool
  | .hGate _ | .sGate _ | .xGate _ | .zGate _ | .blockTransversal _ _ => true
  | .transversalLogicalCNOT _ _ _ => true
  | .transversalLogicalCNOTBatch _ _ _ _ => true
  | _ => false

-- the §5 operational programs are all in the exact fragment:
example : (xhSrc ++ zhSrc ++ xsSrc ++ djConstantSrc).all exactSupportedOp = true := by decide
-- entangling / magic / measurement ops are NOT exact (typechecked / ideal / deferred):
example : exactSupportedOp (.cnotGate ⟨0, 0⟩ ⟨1, 0⟩) = false := by decide
example : exactSupportedOp (.transversalLogicalCNOT ⟨0, 0⟩ ⟨1, 0⟩ [[true]]) = true := by decide
example : exactSupportedOp (.czGate ⟨0, 0⟩ ⟨1, 0⟩) = false := by decide   -- experimental placeholder gadget
example : exactSupportedOp (.tGate ⟨0, 0⟩) = false := by decide           -- deferred magic
example : exactSupportedOp (.measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)]) = false := by decide  -- typechecked, ideal readout

/-! ## §6. Negative source well-formedness (M17 task 2). -/

-- `czGate q q` (control = target) is rejected, just like `cnotGate` …
example : sourceWellFormed [] tenv2 PPMState.init [.czGate ⟨0, 0⟩ ⟨0, 0⟩] = false := by decide
example : sourceWellFormed [] tenv2 PPMState.init [.cnotGate ⟨0, 0⟩ ⟨0, 0⟩] = false := by decide
-- … while a VALID (control ≠ target) `czGate`/`cnotGate` IS well-formed (the check is
-- not over-rejecting — it fires only on `c = t`):
example : sourceWellFormed [] tenv2 PPMState.init [.czGate ⟨0, 0⟩ ⟨1, 0⟩] = true := by decide
example : sourceWellFormed [] tenv2 PPMState.init [.cnotGate ⟨0, 0⟩ ⟨1, 0⟩] = true := by decide
-- malformed `blockTransversal` matrices are rejected (true 2×2 shape required):
example : sourceWellFormed [] tenvQ PPMState.init [.blockTransversal 0 [[true]]] = false := by decide                    -- 1×1
example : sourceWellFormed [] tenvQ PPMState.init [.blockTransversal 0 [[true, false, false], [false, true, false]]] = false := by decide  -- 2×3 rows
example : sourceWellFormed [] tenvQ PPMState.init [.blockTransversal 0 [[true, false], [false, true], [false, false]]] = false := by decide  -- 3 rows
-- a well-shaped 2×2 transversal IS well-formed:
example : sourceWellFormed [] tenvQ PPMState.init [.blockTransversal 0 hGate2x2] = true := by decide

end Compiler.Demo
