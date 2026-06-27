/-
  Compiler.Mixed.Check — the mixed-IR checker + the LEGACY (M9) cost-driven
  selector.

  This file owns (split out of Compiler/Mixed.lean): `checkInstr` /
  `checkLogicalExecAux` / `checkLogicalExec` (the env- and resource-threading
  checker), the `private` legacy cost model (`cost`/`insByCost`/`sortByCost`/
  `firstLegal`/`compileOp`) and the `emitsTransversal`/`emitsPPM` helpers, plus
  the original Mixed.lean executable tests that exercise them.  See
  `Compiler/Mixed.lean` for the module-level design notes.
-/
import Compiler.Mixed.Syntax

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ## §2. The mixed-IR checker (threads the TypedEnv across switches). -/

/-- Check one mixed instruction, threading BOTH the typed environment `Γ` and the
    PPM resource state `st` (bound classical outcomes + DISCARDED logical qubits).
    A PPM fragment runs from the threaded `st` (so a qubit discarded in an EARLIER
    fragment is still dead — use-after-discard is caught ACROSS fragments).
    Transversal/automorphism are non-consuming; a `switch` consumes the source
    CODE, replacing block `b` in place with the target code; `magic` TYPE-CHECKS as
    a DEFERRED obligation (the program is well-typed MODULO an unmet magic-state
    requirement) but carries NO operational semantics — `Step` has no `.magic` rule,
    so a magic-containing program is type-checked but NOT executable (the
    `progress_*` lemmas in MixedSemantics §4 are scoped to the magic-free direct+PPM
    subset; `compile? .executable` excludes magic by construction). -/
def checkInstr (caps : List Capability) :
    TypedEnv → PPMState → MixedInstr → Except TypeError (TypedEnv × PPMState)
  | Γ, st, .ppm s =>
      match checkPPMStmt Γ caps st s with | .ok st' => .ok (Γ, st') | .error e => .error e
  | Γ, st, .transversal b g =>
      -- RESOURCE SOUNDNESS: a direct gate on a block with ANY discarded logical
      -- qubit is rejected (no subblock/renaming rule yet).
      match st.dead.find? (fun q => q.blk == b) with
      | some q => .error (.useAfterDiscard q.blk q.idx)
      | none =>
        match checkTransversal Γ b g with | .ok _ => .ok (Γ, st) | .error e => .error e
  | Γ, st, .automorphism b M =>
      match st.dead.find? (fun q => q.blk == b) with
      | some q => .error (.useAfterDiscard q.blk q.idx)
      | none =>
        match checkLogicalAutomorphism Γ b M with | .ok _ => .ok (Γ, st) | .error e => .error e
  | Γ, st, .switch b D cert =>
      match st.dead.find? (fun q => q.blk == b) with
      | some q => .error (.useAfterDiscard q.blk q.idx)
      | none =>
        match toTargetBlock? D with
        | .error e => .error e
        | .ok tD =>
          match checkSwitch Γ b tD cert with | .ok (Γ', _) => .ok (Γ', st) | .error e => .error e
  | Γ, st, .magic _ => .ok (Γ, st)   -- DEFERRED magic obligation: type-checks (recorded), NO Step semantics
  | Γ, st, .pauli q _ =>
      -- a logical Pauli is APPLIED to a live, in-range logical qubit (M18); same
      -- operand discipline as a PPM `.frame`, but with real Step semantics below.
      if st.dead.contains q then .error (.useAfterDiscard q.blk q.idx)
      else if validLQubit Γ q then .ok (Γ, st) else .error (.badLogicalIndex q.blk q.idx)

/-- Check a whole mixed program, threading the environment AND the PPM resource
    state instruction-to-instruction (a switch's new code is visible downstream;
    a discard in one PPM fragment is visible to later fragments). -/
def checkLogicalExecAux (caps : List Capability) :
    TypedEnv → PPMState → LogicalExec → Except TypeError (TypedEnv × PPMState)
  | Γ, st, []        => .ok (Γ, st)
  | Γ, st, i :: rest =>
      match checkInstr caps Γ st i with
      | .ok (Γ', st') => checkLogicalExecAux caps Γ' st' rest
      | .error e      => .error e

/-- Check a mixed program from the initial resource state; returns the final
    typed environment. -/
def checkLogicalExec (caps : List Capability) (Γ : TypedEnv) (prog : LogicalExec) :
    Except TypeError TypedEnv :=
  (checkLogicalExecAux caps Γ PPMState.init prog).map Prod.fst

/-! ## §3·LEGACY (M9 cost-driven selector).

    `cost`/`firstLegal`/`compileOp` are the original M9 resource-LIGHT selector
    (no threaded resource state).  They are SUPERSEDED by the resource-aware
    `Compiler.compileOpR` / `compileProgram` (M10/M11), which thread the PPM
    resource state `R` and are the PUBLIC compiler contract (soundness, supported
    completeness, progress, and the direct-fragment action theorems
    `compileOpR_*_action_sound` all live there).  These are kept `private` as
    in-file history of the cost model and are not part of the public API. -/

/-- An explicit cost model: a direct transversal is cheapest, an arbitrary
    automorphism next, a code switch moderate, a measurement-based PPM gadget the
    most expensive, a magic obligation effectively unbounded.  `firstLegal` SORTS
    candidates by this `cost`, so the cheapest LEGAL implementation wins — a legal
    transversal is never erased into a PPM gadget. -/
private def cost : MixedInstr → Nat
  | .transversal _ _  => 1
  | .pauli _ _        => 1
  | .automorphism _ _ => 2
  | .switch _ _ _     => 5
  | .ppm _            => 10
  | .magic _          => 1000

/-- Insert into a `cost`-ascending list. -/
private def insByCost (i : MixedInstr) : List MixedInstr → List MixedInstr
  | []      => [i]
  | j :: js => if cost i ≤ cost j then i :: j :: js else j :: insByCost i js

/-- Sort candidates cheapest-first by `cost`. -/
private def sortByCost : List MixedInstr → List MixedInstr
  | []      => []
  | i :: is => insByCost i (sortByCost is)

/-- Try candidates in COST ORDER (cheapest first, via `sortByCost` — so `cost`
    genuinely drives selection); return the first that type-checks under `Γ`. -/
private def firstLegal (caps : List Capability) (Γ : TypedEnv) (cands : List MixedInstr) :
    Except TypeError (MixedInstr × TypedEnv) :=
  go (sortByCost cands)
where
  go : List MixedInstr → Except TypeError (MixedInstr × TypedEnv)
    | []        => .error (.notImplemented "no legal implementation for this logical op")
    | i :: rest =>
        match checkInstr caps Γ PPMState.init i with
        | .ok (Γ', _) => .ok (i, Γ')
        | .error _    => go rest

/-- Compile a single logical op, trying cheaper implementations first.  The
    ancilla qubit `anc` and fresh outcome vars `r₁ r₂ r₃` feed the PPM-gadget
    fallback.  KEY INVARIANT: a legal transversal `H`/`S` is emitted DIRECTLY as a
    `transversal` instruction, never lowered to a PPM gadget. -/
private def compileOp (caps : List Capability) (Γ : TypedEnv) (anc : LQubit) (r₁ r₂ r₃ : CVar) :
    LogicalOp → Except TypeError (MixedInstr × TypedEnv)
  | .measure r P =>
      match checkPPMProgram Γ caps (.meas r P) with
      | .ok _    => .ok (.ppm (.meas r P), Γ)
      | .error e => .error e
  | .hGate q =>
      match checkTransversal Γ q.blk hGate2x2 with                     -- (1) direct transversal
      | .ok _ => .ok (.transversal q.blk hGate2x2, Γ)
      | .error _ =>
        match checkPPMProgram Γ caps (progHAt q anc r₁ r₂) with        -- (2) PPM gadget fallback
        | .ok _    => .ok (.ppm (progHAt q anc r₁ r₂), Γ)
        | .error _ => .error (.notImplemented "H: no legal transversal and no PPM gadget")
  | .sGate q =>
      match checkTransversal Γ q.blk sGate2x2 with
      | .ok _ => .ok (.transversal q.blk sGate2x2, Γ)
      | .error _ =>
        match checkPPMProgram Γ caps (progSAt q anc r₁ r₂) with
        | .ok _    => .ok (.ppm (progSAt q anc r₁ r₂), Γ)
        | .error _ => .error (.notImplemented "S: no legal transversal and no PPM gadget")
  | .cnotGate c t =>
      match checkPPMProgram Γ caps (progCNOTAt c t anc r₁ r₂ r₃) with   -- transversal CNOT deferred
      | .ok _    => .ok (.ppm (progCNOTAt c t anc r₁ r₂ r₃), Γ)
      | .error _ => .error (.notImplemented "CNOT: no PPM gadget (transversal CNOT deferred)")
  | .tGate _ => .error (.notImplemented "T (π/8): magic state required; MagicQ not wired")
  | .blockTransversal _ _ => .error (.notImplemented "blockTransversal: use the public compileOpR")
  | .xGate _ | .zGate _ | .czGate _ _ => .error (.notImplemented "X/Z/CZ: use the public compileOpR")

/-! ## §5. Executable tests (separate from the theorems above). -/

/-- Is the result a DIRECT transversal instruction (not a PPM gadget)? -/
private def emitsTransversal : Except TypeError (MixedInstr × TypedEnv) → Bool
  | .ok (.transversal _ _, _) => true
  | _                         => false

/-- Is the result a PPM gadget? -/
private def emitsPPM : Except TypeError (MixedInstr × TypedEnv) → Bool
  | .ok (.ppm _, _) => true
  | _               => false

-- A legal transversal H on the bare qubit is emitted DIRECTLY, not as PPM:
example : emitsTransversal (compileOp [] tenvQ ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩)) = true := by decide
example : emitsPPM (compileOp [] tenvQ ⟨1, 0⟩ 0 1 2 (.hGate ⟨0, 0⟩)) = false := by decide
-- likewise transversal S:
example : emitsTransversal (compileOp [] tenvQ ⟨1, 0⟩ 0 1 2 (.sGate ⟨0, 0⟩)) = true := by decide

-- FALLBACK: when the transversal candidate is illegal but a capability-backed PPM
-- gadget type-checks, selection falls back to PPM (here the joint-ZZ adapter
-- `zzCap` makes `progS` legal over the two-block env `tenvQR`):
example : emitsPPM (firstLegal [zzCap] tenvQR
    [.transversal 0 (TypeChecker.zeroMat 2 2), .ppm progS]) = true := by decide
-- COST genuinely drives selection: even with the PPM candidate listed FIRST,
-- `firstLegal` sorts by `cost` and picks the cheaper legal transversal:
example : emitsTransversal (firstLegal [] tenvQ
    [.ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)]), .transversal 0 hGate2x2]) = true := by decide

-- NO legal implementation → a typed compiler error (CNOT gadget needs an ancilla
-- block that the single-block env lacks):
example : ok? (compileOp [] tenvQ ⟨1, 0⟩ 0 1 2 (.cnotGate ⟨0, 0⟩ ⟨0, 1⟩)) = false := by decide
-- a T gate is a magic obligation:
example : (match compileOp [] tenvQ ⟨1, 0⟩ 0 1 2 (.tGate ⟨0, 0⟩) with
           | .error (.notImplemented _) => true | _ => false) = true := by decide

-- checkLogicalExec threads the env: a transversal then a measurement, both legal:
example : ok? (checkLogicalExec [] tenvQ
    [.transversal 0 hGate2x2, .ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)])]) = true := by decide
-- strict PPM native targets still reject >2-body / duplicate measurements inside a fragment:
example : ok? (checkLogicalExec [] tenvQR
    [.ppm (.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.Z), (⟨1, 0⟩, PPM.PLetter.X)])]) = false := by decide

-- SWITCH threads the environment (a genuine discriminator): encode the bare
-- qubit (n=1) into the [[3,1,1]] code (n=3), then apply the IDENTITY automorphism
-- `idMat 6` — a 2·3×2·3 map that is well-shaped ONLY for the n=3 post-switch block.
-- It is legal AFTER the switch …
example : ok? (checkLogicalExec [] tsrc
    [.switch 0 repCode3 { kind := .gaugeFix, f := encF }, .automorphism 0 (idMat 6)]) = true := by decide
-- … but the SAME automorphism is illegal WITHOUT the switch (block 0 is still n=1,
-- so `idMat 6` is not 2n×2n) — proving the post-switch env was threaded through:
example : ok? (checkLogicalExec [] tsrc [.automorphism 0 (idMat 6)]) = false := by decide
-- a malformed switch target is rejected (and not reported as the source id):
example : (match checkLogicalExec [] tsrc [.switch 0 { repCode3 with lz := [] } { kind := .gaugeFix, f := encF }] with
           | .error .malformedTarget => true | _ => false) = true := by decide

-- USE-AFTER-DISCARD is caught ACROSS PPM fragments (the threaded resource state):
-- discarding ⟨0,0⟩ in one `.ppm` then measuring it in a later `.ppm` is rejected.
example : ok? (checkLogicalExec [] tenvQ
    [.ppm (.discard ⟨0, 0⟩), .ppm (.meas 4 [(⟨0, 0⟩, PPM.PLetter.Z)])]) = false := by decide

-- RESOURCE SOUNDNESS (M10 Stage 1): a DIRECT operation on a block holding a
-- discarded logical qubit is rejected — transversal, automorphism, and switch all
-- consult the threaded resource state.
example : ok? (checkLogicalExec [] tenvQ
    [.ppm (.discard ⟨0, 0⟩), .transversal 0 hGate2x2]) = false := by decide
example : ok? (checkLogicalExec [] tenvQ
    [.ppm (.discard ⟨0, 0⟩), .automorphism 0 (idMat 2)]) = false := by decide
example : ok? (checkLogicalExec [] tsrc
    [.ppm (.discard ⟨0, 0⟩), .switch 0 repCode3 { kind := .gaugeFix, f := encF }]) = false := by decide

end Compiler
