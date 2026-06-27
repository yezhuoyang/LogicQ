/-
  Compiler.Simulator.ExecMixed — the source-vs-EMITTED execution machinery: the
  layout, the source/emitted decoders (`opGate?`/`sourceGates`/`mixedInstrToGate?`/
  `loweredGates`), and the executable operational interpreter
  (`simPauli`/`simCliff`/`simInterp`/`execInstr`/`execMixed` + alignment), split out
  of Compiler/Simulator.lean.
-/
import Compiler.Simulator.Gate
import Compiler.Mixed
import Compiler.MixedSemantics

namespace Compiler.Sim
open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-! ## §6. Source-vs-EMITTED execution comparison (with an explicit layout).

    A `Layout` maps a LOGICAL qubit `⟨blk, idx⟩` to a SIMULATOR qubit index —
    respecting BOTH block and logical index (so two logicals of the SAME block are
    distinct sim qubits).  `sourceGates` reads the source program's ideal gates;
    `loweredGates` DECODES the EMITTED mixed program (via `compile?`) back to
    gates — a `.transversal` is decoded by its symplectic matrix, exactly the
    realisation `compileOpR_*_action_sound` proves at the symplectic level.

    So the §6 comparison runs the EMITTED instructions, not recorded source ops.
    For the DIRECT fragment this is exact.  A compiled logical PAULI is emitted as a
    `.ppm (.frame q P)` byproduct update; `mixedInstrToGate?` decodes it to the EAGER
    physical Pauli (`X`/`Z`) on the frame's qubit — which gives the SAME FINAL STATE
    as the deferred Pauli-frame model (a Pauli pushed through a Clifford becomes its
    Clifford-conjugate, e.g. `X;H ≡ H;Z` since `HXH = Z`), so the comparison is HONEST
    for the recorded-frame fragment too (M17 task 1).  MULTI-statement PPM gadgets
    (`.meas`/`progHAt`/`progCNOTAt`) are still NOT decoded to a single gate — their
    channel is the deferred ideal-gadget ASSUMPTION (`none`), so a gadget program
    decodes to a SHORTER gate list and we do not assert source = emitted for it. -/

/-- A logical→simulator qubit layout, respecting block AND index. -/
abbrev Layout := LQubit → Nat
/-- A flat layout: `perBlock` sim qubits per block, then the logical index. -/
def Layout.flat (perBlock : Nat) : Layout := fun q => q.blk * perBlock + q.idx

/-- The IDEAL logical gate a SOURCE op realises (`none` for measurement / `T`).  A
    `blockTransversal` on a single-logical block acts on that block's qubit. -/
def opGate? (L : Layout) : LogicalOp → Option Gate
  | .hGate q      => some (.H (L q))
  | .sGate q      => some (.S (L q))
  | .cnotGate c t => some (.CNOT (L c) (L t))
  | .xGate q      => some (.X (L q))
  | .zGate q      => some (.Z (L q))
  | .czGate c t   => some (.CZ (L c) (L t))
  | .blockTransversal b g =>
      if g == hGate2x2 then some (.H (L ⟨b, 0⟩))
      else if g == sGate2x2 then some (.S (L ⟨b, 0⟩)) else none
  | _             => none

/-- The source circuit of a logical program under a layout. -/
def sourceGates (L : Layout) (prog : List LogicalOp) : List Gate := prog.filterMap (opGate? L)

/-- DECODE an EMITTED mixed instruction back to a simulator gate.  A `.transversal`
    is decoded by its symplectic matrix (`hGate2x2`→H, `sGate2x2`→S), acting on the
    block's logical qubit (index 0 in these single-logical fixtures).  A logical Pauli
    `.pauli q P` (emitted by `xGate`/`zGate`, M18) decodes to the physical Pauli on `q`
    — and this decode now AGREES with the real `Step` semantics, which APPLIES the
    Pauli to the carrier (`execMixed`/`simInterp` below), not merely records a frame.
    Multi-stmt PPM gadgets, automorphisms, switches, and magic are NOT decoded (ideal). -/
def mixedInstrToGate? (L : Layout) : MixedInstr → Option Gate
  | .transversal b g =>
      if g == hGate2x2 then some (.H (L ⟨b, 0⟩))
      else if g == sGate2x2 then some (.S (L ⟨b, 0⟩)) else none
  | .pauli q p =>
      match p with
      | .X => some (.X (L q))
      | .Z => some (.Z (L q))
      | .Y => none            -- never emitted by xGate/zGate
  | .ppm (.frame q p) =>      -- a hand-written record-only frame (NOT emitted by the compiler)
      match p with
      | .X => some (.X (L q))
      | .Z => some (.Z (L q))
      | .Y => none
  | _ => none

/-- The decoded circuit of an EMITTED mixed program (direct-fragment instructions). -/
def loweredGates (L : Layout) (prog : LogicalExec) : List Gate := prog.filterMap (mixedInstrToGate? L)

/-! ## §5·M18. An executable interpreter that RUNS the operational semantics.

    `loweredGates` is a DECODER that `filterMap`s — it silently DROPS any instruction
    it cannot decode.  Worse, in M17 a logical Pauli was emitted as a record-only
    `.ppm (.frame …)` whose real `Step` semantics does NOT touch the carrier, so the
    decoder's eager-Pauli reading did not reflect the operational model.

    M18 fixes this at the SOURCE: `xGate`/`zGate` now lower to a real `MixedInstr.pauli`
    whose `Step.pauli` rule APPLIES the Pauli to the carrier.  Here we RUN an emitted
    program through `execMixed`, an executable interpreter:
      * a `.pauli` step is PROVEN equal to the `Step.pauli` carrier update — both are
        `simInterp.pauli` (`step_pauli_matches_exec`).  This is the M18 alignment.
      * a `.transversal b g` step applies the gate's SYMPLECTIC CLIFFORD (`H`/`S`) to
        the BLOCK's logical qubit `L ⟨b,0⟩` (LAYOUT-AWARE), realizing the symplectic
        action of `Step_transversal_realizes`, and is validated OPERATIONALLY against
        the ideal source run (§5 below).  It is NOT pointwise-equal to
        `Step (simInterp …)` on a MULTI-block program: the abstract `MixedInterp.clifford`
        (`simCliff`) is block-LOCAL (it sees only the matrix, not the block index, so it
        acts on qubit `⟨0,0⟩`), whereas `execMixed` is layout-aware — so `execMixed` is
        the faithful per-qubit realization, not a literal `execMixed = Step` equality on
        the transversal fragment.
    Unlike `loweredGates`, `execMixed` returns `none` (STUCK) on an instruction it
    cannot run — it never silently drops. -/

/-- Apply a logical Pauli to the carrier (layout-aware).  This IS `simInterp.pauli`,
    hence exactly the carrier update `Step.pauli` performs (`Y = ZX` up to global phase;
    `xGate`/`zGate` only ever emit `X`/`Z`). -/
def simPauli (L : Layout) (n : Nat) : PPM.PLetter → LQubit → State → State
  | .X, q, s => applyGate n (.X (L q)) s
  | .Z, q, s => applyGate n (.Z (L q)) s
  | .Y, q, s => applyGate n (.Z (L q)) (applyGate n (.X (L q)) s)

/-- Decode a SINGLE-block symplectic Clifford matrix to its gate (block-0 qubit). -/
def simCliff (L : Layout) (n : Nat) (M : BoolMat) (s : State) : State :=
  if M == Internal.transversalMap 1 hGate2x2 then applyGate n (.H (L ⟨0, 0⟩)) s
  else if M == Internal.transversalMap 1 sGate2x2 then applyGate n (.S (L ⟨0, 0⟩)) s
  else s

/-- The simulator `MixedInterp`: Clifford by its symplectic matrix, a logical Pauli
    APPLIED to the carrier, ideal (identity) measurement back-action. -/
def simInterp (L : Layout) (n : Nat) : MixedInterp State where
  clifford := simCliff L n
  pauli := simPauli L n
  qinterp := { proj := fun _ _ s => s }

/-- Run ONE emitted instruction's REAL quantum effect (layout-aware): a `.pauli` is
    APPLIED, a `.transversal` is applied at its block's logical qubit.  Returns `none`
    (STUCK — never dropped) for anything this direct+Pauli fragment does not execute
    (a PPM gadget, automorphism, switch, or magic obligation). -/
def execInstr (L : Layout) (n : Nat) : MixedInstr → State → Option State
  | .pauli q p, s        => some (simPauli L n p q s)
  | .transversal b g, s  =>
      if g == hGate2x2 then some (applyGate n (.H (L ⟨b, 0⟩)) s)
      else if g == sGate2x2 then some (applyGate n (.S (L ⟨b, 0⟩)) s) else none
  | _, _                 => none

/-- Run an emitted program left-to-right; `none` if ANY instruction is not executable
    by this fragment-interpreter (no silent drop, unlike `loweredGates`). -/
def execMixed (L : Layout) (n : Nat) : LogicalExec → State → Option State
  | [],         s => some s
  | i :: rest,  s => match execInstr L n i s with | some s' => execMixed L n rest s' | none => none

/-- **ALIGNMENT (the M18 gap closed).**  The executable `.pauli` step produces EXACTLY
    the carrier the operational `Step.pauli` rule yields — both are `simInterp.pauli`.
    So `execMixed` running an emitted `xGate`/`zGate` genuinely APPLIES the Pauli, in
    agreement with the real `Step` semantics (NOT a record-only frame). -/
theorem step_pauli_matches_exec (L : Layout) (n : Nat) (caps : List Capability)
    (q : LQubit) (p : PPM.PLetter) (s s' : ExecState State)
    (h : Step (simInterp L n) caps (.pauli q p) s s') :
    execInstr L n (.pauli q p) s.quantum = some s'.quantum := by
  rw [Step_pauli_realizes (simInterp L n) caps q p s s' h]; rfl

/-- A direct `H ; S ; H` program (one logical qubit ↔ sim qubit `L ⟨0,0⟩`). -/
def hshProg : List LogicalOp := [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩, .hGate ⟨0, 0⟩]

end Compiler.Sim
