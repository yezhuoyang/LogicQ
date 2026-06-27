/-
  Compiler.Mixed.Lower.ProgramOk — the source PROGRAM typing judgment
  (`Resources`/`progOpOk`/`ProgramOk`/`ProgramOkSupported`) and supported-fragment
  completeness, plus its §3·5 tests (split out of Compiler/Mixed/Lower.lean).
-/
import Compiler.Mixed.Lower.Op
import Compiler.Mixed.Lower.Program

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-- Static compile-time resources a source program is typed against: the ancilla
    qubit feeding gadget fallbacks, and the magic POLICY (whether `T`/π·8
    obligations may be admitted — `false` until `MagicQ` is wired). -/
structure Resources where
  anc        : LQubit
  allowMagic : Bool
  deriving Repr, Inhabited

/-- `Γ; R; fresh ⊢ op ok` — full source-op typing with ALL the M11 conditions:
    valid/live/not-discarded operands (`srcOpOk`), PPM legality + capability
    availability (`checkPPMProgram` under `caps`), CNOT control≠target, the
    T/magic POLICY, the fresh-CVar discipline (a measurement's outcome var is the
    threaded fresh slot and not already bound), and ancilla availability.

    ANCILLA availability is a CONSERVATIVE precondition applied UNIFORMLY to every
    gate op (`H`/`S`/`CNOT`/`T`): `H`/`S` MAY fall back to a teleportation gadget,
    `CNOT` ALWAYS lowers to one, and `T` injection consumes a magic ancilla — so a
    valid ancilla must be available even when the chosen path (a direct transversal
    `H`/`S`) happens not to use it.  A measurement consumes no ancilla.  The
    `! R.bound.contains r` conjunct is belt-and-suspenders: redundant under the
    `PPMState.init`/`fresh`-monotone entry (where `r == fresh` already implies it),
    but it rejects a pre-seeded/non-canonical `bound` at an arbitrary entry. -/
def progOpOk (caps : List Capability) (res : Resources)
    (Γ : TypedEnv) (R : PPMState) (fresh : CVar) : LogicalOp → Bool
  | .measure r P  => srcOpOk Γ R (.measure r P)                  -- valid/live/not-discarded factors
                     && ok? (checkPPMProgram Γ caps (.meas r P)) -- PPM legality + capability availability
                     && (r == fresh) && ! R.bound.contains r     -- fresh-CVar discipline
  | .hGate q      => srcOpOk Γ R (.hGate q) && validLQubit Γ res.anc          -- ancilla (gadget fallback)
  | .sGate q      => srcOpOk Γ R (.sGate q) && validLQubit Γ res.anc
  | .cnotGate c t => srcOpOk Γ R (.cnotGate c t) && (! (c == t)) && validLQubit Γ res.anc  -- control≠target + ancilla
  | .tGate q      => srcOpOk Γ R (.tGate q) && res.allowMagic && validLQubit Γ res.anc      -- T/magic policy + magic ancilla
  | .blockTransversal b g => srcOpOk Γ R (.blockTransversal b g)   -- direct block op: no ancilla needed
  | .xGate q      => srcOpOk Γ R (.xGate q)                        -- Pauli frame update: no ancilla
  | .zGate q      => srcOpOk Γ R (.zGate q)
  | .czGate c t   => srcOpOk Γ R (.czGate c t) && (! (c == t)) && validLQubit Γ res.anc      -- gadget: control≠target + ancilla

/-- `ProgramOk Γ caps res ops`: a whole straight-line source program is well-typed,
    threading `Γ`, the resource state `R`, and the fresh-CVar counter (3 reserved
    per op, matching `compileProgram`). -/
def ProgramOk (caps : List Capability) (res : Resources) :
    TypedEnv → PPMState → CVar → List LogicalOp → Bool
  | _, _, _, []             => true
  | Γ, R, fresh, op :: rest =>
      progOpOk caps res Γ R fresh op && ProgramOk caps res Γ (progOpNext R op) (fresh + 3) rest

/-- The SUPPORTED fragment for whole-program completeness: every op is a
    transversal-LEGAL `H`/`S` on a SINGLE-LOGICAL (`k=1`) live block (the direct
    Clifford-without-CNOT fragment, where a block-wide transversal IS the qubit
    gate).  `Γ` and `R` are INVARIANT across such a program. -/
def ProgramOkSupported (caps : List Capability) (Γ : TypedEnv) (R : PPMState) :
    List LogicalOp → Bool
  | []                => true
  | .hGate q :: rest  => srcOpOk Γ R (.hGate q) && ok? (checkTransversal Γ q.blk hGate2x2)
                         && singleLogicalBlock Γ q.blk && ProgramOkSupported caps Γ R rest
  | .sGate q :: rest  => srcOpOk Γ R (.sGate q) && ok? (checkTransversal Γ q.blk sGate2x2)
                         && singleLogicalBlock Γ q.blk && ProgramOkSupported caps Γ R rest
  | _ :: _            => false

/-- **Supported-fragment completeness.**  If `ProgramOkSupported`, the whole program
    COMPILES — `compileProgram` succeeds and leaves `Γ`/`R` invariant.  Composes
    the per-op progress lemmas (`srcOpOk_*_compiles`) over the program. -/
theorem ProgramOkSupported_compiles (caps : List Capability) (anc : LQubit) :
    ∀ (ops : List LogicalOp) (Γ : TypedEnv) (R : PPMState) (fresh : CVar),
      ProgramOkSupported caps Γ R ops = true →
      ∃ prog, compileProgram caps anc Γ R fresh ops = .ok (prog, Γ, R) := by
  intro ops
  induction ops with
  | nil => intro Γ R fresh _; exact ⟨[], rfl⟩
  | cons op rest ih =>
    intro Γ R fresh h
    cases op with
    | hGate q =>
      simp only [ProgramOkSupported, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hsrc, htrans⟩, hsingle⟩, hrest⟩ := h
      have he : ∃ e, checkTransversal Γ q.blk hGate2x2 = .ok e := by
        cases hh : checkTransversal Γ q.blk hGate2x2 with
        | ok e => exact ⟨e, rfl⟩
        | error e => rw [hh] at htrans; simp [ok?] at htrans
      obtain ⟨e, he⟩ := he
      have hop := srcOpOk_hGate_compiles caps Γ R anc fresh (fresh+1) (fresh+2) q hsingle hsrc he
      obtain ⟨prog', hprog'⟩ := ih Γ R (fresh+3) hrest
      exact ⟨.transversal q.blk hGate2x2 :: prog', by simp only [compileProgram, hop, hprog']⟩
    | sGate q =>
      simp only [ProgramOkSupported, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hsrc, htrans⟩, hsingle⟩, hrest⟩ := h
      have he : ∃ e, checkTransversal Γ q.blk sGate2x2 = .ok e := by
        cases hh : checkTransversal Γ q.blk sGate2x2 with
        | ok e => exact ⟨e, rfl⟩
        | error e => rw [hh] at htrans; simp [ok?] at htrans
      obtain ⟨e, he⟩ := he
      have hop := srcOpOk_sGate_compiles caps Γ R anc fresh (fresh+1) (fresh+2) q hsingle hsrc he
      obtain ⟨prog', hprog'⟩ := ih Γ R (fresh+3) hrest
      exact ⟨.transversal q.blk sGate2x2 :: prog', by simp only [compileProgram, hop, hprog']⟩
    | measure r P  => simp only [ProgramOkSupported] at h; exact absurd h (by simp)
    | cnotGate c t => simp only [ProgramOkSupported] at h; exact absurd h (by simp)
    | tGate q      => simp only [ProgramOkSupported] at h; exact absurd h (by simp)
    | blockTransversal b g => simp only [ProgramOkSupported] at h; exact absurd h (by simp)
    | xGate q      => simp only [ProgramOkSupported] at h; exact absurd h (by simp)
    | zGate q      => simp only [ProgramOkSupported] at h; exact absurd h (by simp)
    | czGate c t   => simp only [ProgramOkSupported] at h; exact absurd h (by simp)

/-! ## §3·5 tests. -/

-- The supported fragment: a direct transversal-`H`/`S` program type-checks AND compiles.
example : ProgramOkSupported [] tenvQ PPMState.init
    [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩, .hGate ⟨0, 0⟩] = true := by decide
-- CNOT / T / measure are NOT in the supported fragment (direct H/S only):
example : ProgramOkSupported [] tenvQ PPMState.init [.cnotGate ⟨0, 0⟩ ⟨0, 1⟩] = false := by decide
example : ProgramOkSupported [] tenvQ PPMState.init [.tGate ⟨0, 0⟩] = false := by decide

-- `ProgramOk`: a fresh-disciplined measurement program is well-typed.
example : ProgramOk [] ⟨⟨0, 0⟩, false⟩ tenvQ PPMState.init 0
    [.measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)]] = true := by decide
-- T/magic policy: `T` rejected when `allowMagic = false`, accepted when `true`.
example : ProgramOk [] ⟨⟨0, 0⟩, false⟩ tenvQ PPMState.init 0 [.tGate ⟨0, 0⟩] = false := by decide
example : ProgramOk [] ⟨⟨0, 0⟩, true⟩  tenvQ PPMState.init 0 [.tGate ⟨0, 0⟩] = true := by decide
-- CNOT control = target is rejected.
example : ProgramOk [] ⟨⟨0, 0⟩, false⟩ tenvQ PPMState.init 0 [.cnotGate ⟨0, 0⟩ ⟨0, 0⟩] = false := by decide
-- fresh-CVar discipline: a measurement's outcome var must be the threaded fresh slot.
example : ProgramOk [] ⟨⟨0, 0⟩, false⟩ tenvQ PPMState.init 0
    [.measure 5 [(⟨0, 0⟩, PPM.PLetter.Z)]] = false := by decide

end Compiler
