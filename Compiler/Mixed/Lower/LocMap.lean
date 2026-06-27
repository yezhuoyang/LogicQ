/-
  Compiler.Mixed.Lower.LocMap — the logical LOCATION / alias map for PPM
  teleportation gadgets (`LocMap` + `compileProgramLoc` + soundness) and its §3·6
  tests (split out of Compiler/Mixed/Lower.lean).
-/
import Compiler.Mixed.Lower.Op

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ## §3·6. Logical LOCATION / alias map for PPM teleportation gadgets.

    A PPM `H`/`S` gadget TELEPORTS the logical state onto an ancilla (the canonical
    logical qubit `q` now lives at `anc`).  `LocMap` records where each canonical
    logical qubit currently lives; the H/S PPM-FALLBACK relocates `q ↦ anc`, and
    downstream ops RESOLVE their operands through the map.  A DIRECT transversal
    does not teleport, so it leaves the map put. -/

/-- Canonical logical name ↦ current physical location. -/
abbrev LocMap := List (LQubit × LQubit)

/-- Where a canonical logical qubit currently lives (itself, if never relocated). -/
def LocMap.loc (m : LocMap) (q : LQubit) : LQubit :=
  match m.find? (fun p => p.1 == q) with
  | some p => p.2
  | none   => q

/-- Relocate canonical qubit `q` to live at `anc`. -/
def LocMap.relocate (q anc : LQubit) (m : LocMap) : LocMap :=
  (q, anc) :: m.filter (fun p => ! (p.1 == q))

/-- Resolve an op's operands through the current location map. -/
def LogicalOp.resolve (m : LocMap) : LogicalOp → LogicalOp
  | .measure r P  => .measure r (P.map (fun f => (m.loc f.1, f.2)))
  | .hGate q      => .hGate (m.loc q)
  | .sGate q      => .sGate (m.loc q)
  | .cnotGate c t => .cnotGate (m.loc c) (m.loc t)
  | .tGate q      => .tGate (m.loc q)
  | .blockTransversal b g => .blockTransversal b g   -- block-level: no per-qubit alias to resolve
  | .xGate q      => .xGate (m.loc q)
  | .zGate q      => .zGate (m.loc q)
  | .czGate c t   => .czGate (m.loc c) (m.loc t)

/-- The location update an emitted instruction induces: an `H`/`S` PPM gadget (the
    fallback) teleports the logical qubit to `anc`, relocating the CANONICAL name;
    a direct transversal (or anything else) leaves the map unchanged.

    CRITICAL: this MUST be applied to the ORIGINAL (canonical) op, NOT the
    resolved op — otherwise a second fallback would relocate the resolved
    intermediate (`q1`) instead of the canonical name (`q0`), so `q0 ↦ q1 ↦ q2`
    would leave `loc q0 = q1` (stale).  `relocate` replaces any existing binding
    for the canonical name, so relocating the canonical name keeps `loc` direct
    (no chains form) and `q0 ↦ q1 ↦ q2` correctly resolves `loc q0 = q2`. -/
def relocateOnFallback (anc : LQubit) : LogicalOp → MixedInstr → LocMap → LocMap
  | .hGate q, .ppm _, m => m.relocate q anc
  | .sGate q, .ppm _, m => m.relocate q anc
  | _,        _,      m => m

/-- `compileProgram` threading the location map: each op's operands are RESOLVED
    through the map before compilation, and an H/S fallback relocates the CANONICAL
    qubit (the original op's name, not the resolved one) to the ancilla. -/
def compileProgramLoc (caps : List Capability) (anc : LQubit) :
    TypedEnv → PPMState → CVar → LocMap → List LogicalOp →
    Except TypeError (LogicalExec × TypedEnv × PPMState × LocMap)
  | Γ, R, _, m, []          => .ok ([], Γ, R, m)
  | Γ, R, fresh, m, op :: rest =>
      -- compile the RESOLVED op; relocate the CANONICAL name (`op`, not the resolved one)
      match compileOpR caps Γ R anc fresh (fresh + 1) (fresh + 2) (op.resolve m) with
      | .error e => .error e
      | .ok (instr, Γ', R') =>
        match compileProgramLoc caps anc Γ' R' (fresh + 3) (relocateOnFallback anc op instr m) rest with
        | .error e => .error e
        | .ok (instrs, Γ'', R'', m'') => .ok (instr :: instrs, Γ'', R'', m'')

/-! ## §3·6 tests. -/

-- Default: an unrelocated logical qubit lives at itself.
example : LocMap.loc [] ⟨0, 0⟩ = ⟨0, 0⟩ := by decide
-- Relocation: `q ↦ anc`, and a downstream op resolves to the ancilla.
example : LocMap.loc (LocMap.relocate ⟨0, 0⟩ ⟨1, 0⟩ []) ⟨0, 0⟩ = ⟨1, 0⟩ := by decide
example : (match (LogicalOp.hGate ⟨0, 0⟩).resolve (LocMap.relocate ⟨0, 0⟩ ⟨1, 0⟩ []) with
           | .hGate q => q == ⟨1, 0⟩ | _ => false) = true := by decide
-- An H PPM-FALLBACK (a `.ppm` gadget) relocates `q ↦ anc`…
example : LocMap.loc (relocateOnFallback ⟨1, 0⟩ (.hGate ⟨0, 0⟩)
    (.ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)])) []) ⟨0, 0⟩ = ⟨1, 0⟩ := by decide
-- …while a DIRECT transversal `H` does NOT teleport (the qubit stays put).
example : LocMap.loc (relocateOnFallback ⟨1, 0⟩ (.hGate ⟨0, 0⟩) (.transversal 0 hGate2x2) [])
    ⟨0, 0⟩ = ⟨0, 0⟩ := by decide
-- compileProgramLoc threads the map: a transversal-H program teleports nothing.
example : (match compileProgramLoc [] ⟨1, 0⟩ tenvQ PPMState.init 0 [] [.hGate ⟨0, 0⟩] with
           | .ok (_, _, _, m) => m.length == 0 | _ => false) = true := by decide

-- REGRESSION (q0 ↦ q1 ↦ q2): two H PPM-fallbacks on the SAME canonical qubit ⟨0,0⟩
-- (relocating to ⟨1,0⟩ then ⟨2,0⟩) resolve transitively — `loc` gives the LATEST
-- ancilla ⟨2,0⟩, never the stale intermediate ⟨1,0⟩.  (Pre-fix, relocating the
-- RESOLVED name would have left `loc ⟨0,0⟩ = ⟨1,0⟩`.)
example :
    let m1 := relocateOnFallback ⟨1, 0⟩ (.hGate ⟨0, 0⟩) (.ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)])) []
    let m2 := relocateOnFallback ⟨2, 0⟩ (.hGate ⟨0, 0⟩) (.ppm (.meas 1 [(⟨0, 0⟩, PPM.PLetter.Z)])) m1
    LocMap.loc m2 ⟨0, 0⟩ = ⟨2, 0⟩ ∧ LocMap.loc m2 ⟨1, 0⟩ = ⟨1, 0⟩ := by decide

/-- **`compileProgramLoc` is SOUND**: the emitted program TYPE-CHECKS from the initial
    environment/resource state — so every emitted instruction is accepted by its
    TypeChecker judgment and (via `checkInstr`'s dead-guards +
    `checkPPMStmt_no_use_after_discard`) uses no discarded logical resource.  The
    location map is threaded ORTHOGONALLY to type-checking (operands are resolved
    before compilation; aliases never affect acceptance). -/
theorem compileProgramLoc_sound (caps : List Capability) (anc : LQubit) :
    ∀ (ops : List LogicalOp) (Γ : TypedEnv) (R : PPMState) (fresh : CVar) (m : LocMap)
      {prog : LogicalExec} {Γ' : TypedEnv} {R' : PPMState} {m' : LocMap},
      compileProgramLoc caps anc Γ R fresh m ops = .ok (prog, Γ', R', m') →
      checkLogicalExecAux caps Γ R prog = .ok (Γ', R') := by
  intro ops
  induction ops with
  | nil =>
    intro Γ R fresh m prog Γ' R' m' h
    simp only [compileProgramLoc, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, _⟩ := h; rfl
  | cons op rest ih =>
    intro Γ R fresh m prog Γ' R' m' h
    simp only [compileProgramLoc] at h
    cases hc : compileOpR caps Γ R anc fresh (fresh + 1) (fresh + 2) (op.resolve m) with
    | error e => simp only [hc] at h; exact absurd h (by simp)
    | ok p1 =>
      obtain ⟨instr, Γ₁, R₁⟩ := p1
      cases hrest : compileProgramLoc caps anc Γ₁ R₁ (fresh + 3)
          (relocateOnFallback anc op instr m) rest with
      | error e => simp only [hc, hrest] at h; exact absurd h (by simp)
      | ok p2 =>
        obtain ⟨instrs, Γ₂, R₂, m₂⟩ := p2
        simp only [hc, hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, _⟩ := h
        have hi := compileOp_sound caps Γ R anc fresh (fresh + 1) (fresh + 2) (op.resolve m) hc
        simp only [checkLogicalExecAux, hi]
        exact ih _ _ _ _ hrest

end Compiler
