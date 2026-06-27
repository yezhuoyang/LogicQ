/-
  TypeChecker.Judgment.PPMProgram.Check — the statement/program well-formedness
  checker and the site collectors used by soundness.
-/
import TypeChecker.Judgment.PPMProgram.State
import TypeChecker.Judgment.PPM

namespace TypeChecker
open ChainQ.GF2 Logical PPM

/-- Well-formedness of a PPM statement over a typed env, threading the program
    state.  (Explicit matches, not `do`, so soundness can `split`.) -/
def checkPPMStmt (Γ : TypedEnv) (caps : List Capability) :
    PPMState → Stmt → Except TypeError PPMState
  | st, .meas r P =>
      match (P.map Prod.fst).find? (fun q => st.dead.contains q) with
      | some q => .error (.useAfterDiscard q.blk q.idx)   -- measures a discarded qubit
      | none =>
        match checkPPM Γ caps P with                      -- measurement must be legal
        | .ok _    => .ok { st with bound := r :: st.bound }
        | .error e => .error e
  | st, .frame q _ =>
      if st.dead.contains q then .error (.useAfterDiscard q.blk q.idx)
      else if validLQubit Γ q then .ok st else .error (.badLogicalIndex q.blk q.idx)
  | st, .discard q =>
      if st.dead.contains q then .error (.useAfterDiscard q.blk q.idx)   -- no double-discard
      else if validLQubit Γ q then .ok { st with dead := DeadSet.insert q st.dead }
      else .error (.badLogicalIndex q.blk q.idx)
  | st, .ite r s₁ s₂ =>
      if !st.bound.contains r then .error (.unboundOutcome r)
      else
        match checkPPMStmt Γ caps st s₁ with
        | .error e => .error e
        | .ok st₁ =>
          match checkPPMStmt Γ caps st s₂ with
          | .error e => .error e
          -- branch-local bindings do not escape; a qubit discarded in EITHER
          -- branch is conservatively treated as dead afterwards (set UNION).
          | .ok st₂  => .ok { bound := st.bound, dead := DeadSet.union st₁.dead st₂.dead }
  | st, .forLoop _ body =>
      match checkPPMStmt Γ caps st body with
      | .error e => .error e
      | .ok st'  =>
        if DeadSet.subset st'.dead st.dead then .ok st'   -- body discards nothing (SET compare)
        else .error (.other "loop body must not discard a logical qubit")
  | st, .skip => .ok st
  | st, .seq s₁ s₂ =>
      match checkPPMStmt Γ caps st s₁ with
      | .error e => .error e
      | .ok st₁  => checkPPMStmt Γ caps st₁ s₂            -- sequencing threads the state
  | st, .abort => .ok st

/-- A PPM PROGRAM is well-formed iff `checkPPMStmt` succeeds from the initial state. -/
def checkPPMProgram (Γ : TypedEnv) (caps : List Capability) (s : Stmt) :
    Except TypeError PPMState :=
  checkPPMStmt Γ caps PPMState.init s

/-! ## Site collectors (for the soundness theorems). -/

/-- Every measurement target appearing in a statement. -/
def measTargets : Stmt → List MTarget
  | .meas _ P    => [P]
  | .frame _ _   => []
  | .discard _   => []
  | .ite _ s₁ s₂ => measTargets s₁ ++ measTargets s₂
  | .forLoop _ b => measTargets b
  | .skip        => []
  | .seq s₁ s₂   => measTargets s₁ ++ measTargets s₂
  | .abort       => []

/-- Every logical qubit touched by a `frame`/`discard`. -/
def frameDiscardTargets : Stmt → List LQubit
  | .meas _ _    => []
  | .frame q _   => [q]
  | .discard q   => [q]
  | .ite _ s₁ s₂ => frameDiscardTargets s₁ ++ frameDiscardTargets s₂
  | .forLoop _ b => frameDiscardTargets b
  | .skip        => []
  | .seq s₁ s₂   => frameDiscardTargets s₁ ++ frameDiscardTargets s₂
  | .abort       => []

/-- Whether a statement REFERENCES logical qubit `q` (measures, frames, or
    discards it). -/
def touches : Stmt → LQubit → Bool
  | .meas _ P,    q => (P.map Prod.fst).contains q
  | .frame q' _,  q => decide (q' = q)
  | .discard q',  q => decide (q' = q)
  | .ite _ s₁ s₂, q => touches s₁ q || touches s₂ q
  | .forLoop _ b, q => touches b q
  | .skip,        _ => false
  | .seq s₁ s₂,   q => touches s₁ q || touches s₂ q
  | .abort,       _ => false

end TypeChecker
