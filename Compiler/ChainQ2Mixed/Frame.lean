/-
  Compiler.ChainQ2Mixed.Frame — classical FRAME / feed-forward typing.

  QGPU, PPM-CNOT, magic/T, and dimension jump all rely on measurement OUTCOMES
  controlling Pauli/Clifford frame updates on the live logical carriers.  This module
  gives that feed-forward a STATIC type discipline:

    * a `bind` binds a fresh measurement-outcome variable (SSA — no duplicate binding);
    * an `applyIf v q p` (conditioned frame update) requires `v` to be BOUND BEFORE USE,
      and targets the LIVE logical carrier of `q` resolved THROUGH the `LocMap` (a frame
      update to a dead / out-of-range carrier is rejected);
    * the accumulated frame is PRESERVED in the checked artifact `FrameState.frame`.

  This is the static-semantics layer; the operational byproduct semantics is the
  existing `PPM.Frame`/`Frame.mulAt` (the `progH_frame` table) — NOT re-modeled here.
-/
import Compiler.Mixed.Lower.LocMap
import TypeChecker.Judgment.PPMProgram.State

namespace Compiler.ChainQ2Mixed.Frame
open Compiler TypeChecker Logical PPM ChainQ.GF2

/-! ## §F.1. Frame expressions + state. -/

/-- A classical feed-forward instruction. -/
inductive FrameExpr
  /-- bind a fresh measurement-outcome variable `v` (SSA). -/
  | bind    (v : CVar)
  /-- if outcome `v` is `-1`, apply Pauli `p` to the logical carrier of `q` (a frame update). -/
  | applyIf (v : CVar) (q : LQubit) (p : PLetter)
  deriving Repr, DecidableEq

/-- The static frame state: the bound outcome variables (SSA) and the accumulated frame
    (the byproduct Pauli on each targeted carrier), PRESERVED for the compiled artifact. -/
structure FrameState where
  bound : List CVar
  frame : List (LQubit × PLetter)
  deriving Repr, DecidableEq

def FrameState.init : FrameState := { bound := [], frame := [] }

/-! ## §F.2. The frame typing checker. -/

/-- Type-check one feed-forward instruction against the env, the location map (resolving
    carriers), and the dead set.  `bind` rejects a re-bound variable (SSA); `applyIf`
    requires the variable BOUND and the resolved carrier VALID + LIVE. -/
def checkFrameExpr (Γ : TypedEnv) (loc : LocMap) (dead : List LQubit) (st : FrameState) :
    FrameExpr → Except TypeError FrameState
  | .bind v =>
      if st.bound.contains v then .error (.outcomeReused v)
      else .ok { st with bound := st.bound ++ [v] }
  | .applyIf v q p =>
      if !st.bound.contains v then .error (.unboundOutcome v)
      else
        let carrier := loc.loc q
        if !validLQubit Γ carrier then .error (.badLogicalIndex carrier.blk carrier.idx)
        else if dead.contains carrier then
          .error (.other "frame update targets a dead logical carrier")
        else .ok { st with frame := st.frame ++ [(carrier, p)] }

/-- Type-check a whole feed-forward program, threading the frame state. -/
def checkFrameProgram (Γ : TypedEnv) (loc : LocMap) (dead : List LQubit) :
    List FrameExpr → FrameState → Except TypeError FrameState
  | [],        st => .ok st
  | e :: rest, st =>
      match checkFrameExpr Γ loc dead st e with
      | .ok st'  => checkFrameProgram Γ loc dead rest st'
      | .error x => .error x

/-! ## §F.3. Soundness — bind-before-use, no-dup, live-carrier frame updates, preservation. -/

/-- **No duplicate binding (SSA).**  An accepted `bind v` had `v` UNBOUND — a re-bind is
    rejected (`outcomeReused`), so outcome variables are bound at most once. -/
theorem checkFrameExpr_bind_fresh {Γ loc dead} {st st' : FrameState} {v : CVar}
    (h : checkFrameExpr Γ loc dead st (.bind v) = .ok st') :
    st.bound.contains v = false ∧ st'.bound = st.bound ++ [v] := by
  simp only [checkFrameExpr] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hc
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by simpa using hc, rfl⟩

/-- **Bind-before-use.**  An accepted `applyIf v …` requires `v` to be ALREADY bound. -/
theorem checkFrameExpr_applyIf_bound {Γ loc dead} {st st' : FrameState} {v q p}
    (h : checkFrameExpr Γ loc dead st (.applyIf v q p) = .ok st') : st.bound.contains v = true := by
  simp only [checkFrameExpr] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hb; simpa using hb

/-- **Frame updates target a LIVE carrier through the LocMap.**  An accepted `applyIf v q p`
    resolves `q` through `loc` to a VALID logical carrier that is NOT dead, and records the
    byproduct on that carrier (frame PRESERVED). -/
theorem checkFrameExpr_applyIf_live {Γ loc dead} {st st' : FrameState} {v q p}
    (h : checkFrameExpr Γ loc dead st (.applyIf v q p) = .ok st') :
    validLQubit Γ (loc.loc q) = true ∧ dead.contains (loc.loc q) = false ∧
      st'.frame = st.frame ++ [(loc.loc q, p)] := by
  simp only [checkFrameExpr] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hv hd
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨by simpa using hv, by simpa using hd, rfl⟩

/-! ## §F.4. Tests. -/

-- a tiny 1-logical env (block 0 has one logical qubit) + identity LocMap.
def fEnv : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [{ n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }] } with
  | .ok Γ => Γ | .error _ => { blocks := [] }
def q0 : LQubit := ⟨0, 0⟩

-- bind 0, then a conditioned frame update on q0 (bound + live) — ACCEPTED:
example : ok? (checkFrameProgram fEnv [] [] [.bind 0, .applyIf 0 q0 .X] FrameState.init) = true := by decide
-- UNBOUND outcome variable is REJECTED (use before bind):
example : ok? (checkFrameProgram fEnv [] [] [.applyIf 0 q0 .X] FrameState.init) = false := by decide
-- DUPLICATE binding is REJECTED (SSA):
example : ok? (checkFrameProgram fEnv [] [] [.bind 0, .bind 0] FrameState.init) = false := by decide
-- frame update to a DEAD carrier is REJECTED:
example : ok? (checkFrameProgram fEnv [] [q0] [.bind 0, .applyIf 0 q0 .X] FrameState.init) = false := by decide
-- frame update to an OUT-OF-RANGE carrier is REJECTED:
example : ok? (checkFrameProgram fEnv [] [] [.bind 0, .applyIf 0 ⟨0, 9⟩ .X] FrameState.init) = false := by decide
-- the frame is PRESERVED in the accepted artifact:
example : (match checkFrameProgram fEnv [] [] [.bind 0, .applyIf 0 q0 .X] FrameState.init with
           | .ok st => st.frame | .error _ => []) = [(q0, .X)] := by decide
-- a LocMap relocation retargets the frame update to the CURRENT carrier (q0 ↦ ⟨0,0⟩ via loc):
example : ok? (checkFrameProgram fEnv [(q0, q0)] [] [.bind 1, .applyIf 1 q0 .Z] FrameState.init) = true := by decide

end Compiler.ChainQ2Mixed.Frame
