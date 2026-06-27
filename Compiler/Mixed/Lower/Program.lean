/-
  Compiler.Mixed.Lower.Program — `compileProgram` (threading Γ, resources, and
  fresh classical vars) and its soundness theorem (split out of
  Compiler/Mixed/Lower.lean).
-/
import Compiler.Mixed.Lower.Op

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ## §3. `compileProgram` — thread Γ, resources, and fresh classical vars. -/

/-- Compile a straight-line source program, threading the typed environment, the
    PPM resource state, and a fresh-classical-variable counter (3 reserved per op
    for gadget outcomes); the ancilla qubit is supplied.  Each op is lowered by
    the sound `compileOpR`. -/
def compileProgram (caps : List Capability) (anc : LQubit) :
    TypedEnv → PPMState → CVar → List LogicalOp →
    Except TypeError (LogicalExec × TypedEnv × PPMState)
  | Γ, R, _, [] => .ok ([], Γ, R)
  | Γ, R, fresh, op :: rest =>
      match compileOpR caps Γ R anc fresh (fresh+1) (fresh+2) op with
      | .error e => .error e
      | .ok (instr, Γ', R') =>
        match compileProgram caps anc Γ' R' (fresh+3) rest with
        | .error e => .error e
        | .ok (instrs, Γ'', R'') => .ok (instr :: instrs, Γ'', R'')

/-- **`compileProgram` is sound**: a compiled program TYPE-CHECKS — it is accepted
    by `checkLogicalExecAux` from the same environment and resource state.
    (Composes `compileOp_sound` over the program.) -/
theorem compileProgram_sound (caps : List Capability) (anc : LQubit) :
    ∀ (ops : List LogicalOp) (Γ : TypedEnv) (R : PPMState) (fresh : CVar)
      {prog : LogicalExec} {Γ' : TypedEnv} {R' : PPMState},
      compileProgram caps anc Γ R fresh ops = .ok (prog, Γ', R') →
      checkLogicalExecAux caps Γ R prog = .ok (Γ', R') := by
  intro ops
  induction ops with
  | nil =>
    intro Γ R fresh prog Γ' R' h
    simp only [compileProgram, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | cons op rest ih =>
    intro Γ R fresh prog Γ' R' h
    simp only [compileProgram] at h
    cases hc : compileOpR caps Γ R anc fresh (fresh+1) (fresh+2) op with
    | error e => simp only [hc] at h; exact absurd h (by simp)
    | ok p1 =>
      obtain ⟨instr, Γ₁, R₁⟩ := p1
      cases hrest : compileProgram caps anc Γ₁ R₁ (fresh+3) rest with
      | error e => simp only [hc, hrest] at h; exact absurd h (by simp)
      | ok p2 =>
        obtain ⟨instrs, Γ₂, R₂⟩ := p2
        simp only [hc, hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hi := compileOp_sound caps Γ R anc fresh (fresh+1) (fresh+2) op hc
        simp only [checkLogicalExecAux, hi]
        exact ih _ _ _ hrest

end Compiler
