/-
  Compiler.Mixed.Source — source-level typing of the `LogicalOp` language.

  This file owns the source-side judgments split out of Compiler/Mixed.lean and
  Compiler/MixedSemantics.lean: the intended symplectic action `LogicalOp.srcAction`
  (moved here from Mixed.lean), the per-op well-formedness `srcOpOk`, the
  source-level resource update `progOpNext` (moved EARLY — it depends only on
  `LogicalOp`+`PPMState` and is used by `sourceWellFormed`, so it lives here and is
  imported by `Compiler.Mixed.Lower` without a back-edge), the unified per-op
  source check `sourceOpOk`, and the whole-program operand check `sourceWellFormed`.
-/
import Compiler.Mixed.Syntax

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-- The intended symplectic action of a source logical gate (`none` for the
    fragments we do not yet give a direct unitary action — measure/CNOT/T).
    `blockTransversal b g` always acts BLOCK-WIDE.  `hGate q`/`sGate q` are
    single-LOGICAL ops: their block-wide `transversalMap` action is the intended
    one ONLY when `q`'s block is single-logical (`k = 1`); on a multi-logical block
    we do NOT pretend a per-qubit gate has block-wide action (`none`). -/
def LogicalOp.srcAction (Γ : TypedEnv) : LogicalOp → Option BoolMat
  | .hGate q => if singleLogicalBlock Γ q.blk then
                  (Γ.block? q.blk).map (fun tb => Internal.transversalMap tb.block.n hGate2x2) else none
  | .sGate q => if singleLogicalBlock Γ q.blk then
                  (Γ.block? q.blk).map (fun tb => Internal.transversalMap tb.block.n sGate2x2) else none
  | .blockTransversal b g => (Γ.block? b).map (fun tb => Internal.transversalMap tb.block.n g)
  | _        => none

-- (The LEGACY `compileOp_{h,s}Gate_transversal_sound` action lemmas were removed in
-- M14: `srcAction` for `hGate`/`sGate` is now CONDITIONAL on `singleLogicalBlock`,
-- and the unguarded legacy `compileOp` selector no longer matches it.  The public,
-- guarded path is covered by `Compiler.compileOpR_{h,s}Gate_action_sound`.)

/-! ## §1. Source typing judgments  `Γ; R ⊢ op ok`  and  `… ⊢ program ok`. -/

/-- `Γ; R ⊢ op ok`: every logical qubit the op touches is valid (live, in range)
    in `Γ`, and the RESOURCE precondition the checker uses holds — a measurement's
    factor qubits are not discarded (qubit-level, matching `checkPPMStmt`), and a
    DIRECT gate's block carries no discarded qubit (block-level, matching
    `checkInstr`).  This is source WELL-FORMEDNESS: it is necessary, and (via
    `srcOpOk_hGate_compiles`) drives compilation of the implementable fragment — a
    well-formed `tGate` still yields a magic OBLIGATION, not a compiled instruction. -/
def srcOpOk (Γ : TypedEnv) (R : PPMState) : LogicalOp → Bool
  | .measure _ P  => (P.map Prod.fst).all (fun q => validLQubit Γ q && ! R.dead.contains q)
  | .hGate q      => validLQubit Γ q && ! R.dead.hasBlock q.blk
  | .sGate q      => validLQubit Γ q && ! R.dead.hasBlock q.blk
  | .cnotGate c t => validLQubit Γ c && validLQubit Γ t && ! R.dead.hasBlock c.blk && ! R.dead.hasBlock t.blk
  | .tGate q      => validLQubit Γ q && ! R.dead.hasBlock q.blk
  | .blockTransversal b g => (Γ.block? b).isSome && g.length == 2
                             && g.all (fun row => row.length == 2)   -- TRUE 2×2 shape (M17 task 2)
                             && ! R.dead.hasBlock b
  | .xGate q      => validLQubit Γ q && ! R.dead.hasBlock q.blk
  | .zGate q      => validLQubit Γ q && ! R.dead.hasBlock q.blk
  | .czGate c t   => validLQubit Γ c && validLQubit Γ t && ! R.dead.hasBlock c.blk && ! R.dead.hasBlock t.blk

/-- Source-level resource update after an op (a measurement binds its outcome var;
    direct gates leave the source resource state unchanged). -/
def progOpNext (R : PPMState) : LogicalOp → PPMState
  | .measure r _ => { R with bound := r :: R.bound }
  | _            => R

/-- Per-op SOURCE typecheck (shared by BOTH modes): operands are valid/live and not
    discarded (`srcOpOk` — this REJECTS a bad logical index), a CNOT has
    control ≠ target, and a measurement is PPM-legal.  Operand-level well-formedness;
    the magic policy is the MODE, not checked here. -/
def sourceOpOk (caps : List Capability) (Γ : TypedEnv) (R : PPMState) : LogicalOp → Bool
  | .measure r P  => srcOpOk Γ R (.measure r P) && ok? (checkPPMProgram Γ caps (.meas r P))
  | .cnotGate c t => srcOpOk Γ R (.cnotGate c t) && (! (c == t))
  | .czGate c t   => srcOpOk Γ R (.czGate c t) && (! (c == t))   -- CZ ⟨q⟩⟨q⟩ rejected like CNOT (M17 task 2)
  | op            => srcOpOk Γ R op

/-- **`sourceWellFormed`** — whole-program OPERAND well-formedness (threads the
    resource state).  This checks ONLY that operands are valid/live and a CNOT/CZ has
    control ≠ target.  It does NOT check that each op has an available IMPLEMENTATION
    (a legal lowering on this `Γ`/`caps`) — that stronger property is
    `sourceCompilable` (= `compile?` succeeds).  So `sourceWellFormed ⊋ sourceCompilable`:
    e.g. `hGate` on a multi-logical block with no available gadget ancilla is
    well-formed but NOT compilable. -/
def sourceWellFormed (caps : List Capability) : TypedEnv → PPMState → List LogicalOp → Bool
  | _, _, []         => true
  | Γ, R, op :: rest => sourceOpOk caps Γ R op && sourceWellFormed caps Γ (progOpNext R op) rest

end Compiler
