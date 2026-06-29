/-
  Compiler.Mixed.Syntax — the mixed-IR data layer.

  This file owns the pure DATA + structural maps of the mixed logical-execution IR
  (split out of Compiler/Mixed.lean): the magic obligation, the `MixedInstr`
  instruction set, the source `LogicalOp` language, the single-qubit symplectic
  gate matrices, the symplectic `MixedInstr.action`, and the `singleLogicalBlock`
  predicate.  See `Compiler/Mixed.lean` for the original module-level design notes.
-/
import TypeChecker.Basic
import PPM.Basic

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical
-- NOTE: block ids are written as `Nat` (not `BlockId`) to avoid the harmless
-- `Logical.BlockId` / `TypeChecker.BlockId` name clash (both abbreviate `Nat`).

/-! ## §1. The mixed logical-execution IR. -/

/-- The kind of non-Clifford gate a magic obligation discharges. -/
inductive MagicKind
  | tGate        -- π/8 (T)
  deriving DecidableEq, Repr, Inhabited

/-- A TYPED magic-state obligation (M14): which non-Clifford gate, on which logical
    qubit, and the resource it requires.  Replaces the old bare `String` payload so
    the obligation carries its target/kind (a magic-state factory must later
    discharge it).  It type-checks but has NO `Step` semantics (MagicQ unwired). -/
structure MagicObligation where
  kind               : MagicKind
  target             : LQubit            -- the logical qubit the gate acts on
  requiresMagicState : Bool := true      -- the required resource (a |T⟩/|H⟩ magic state)
  deriving Repr, DecidableEq

/-- One instruction of the mixed IR.  PPM is just one form among several. -/
inductive MixedInstr
  | ppm          (s : PPM.Stmt)                          -- a native PPM/PPU fragment
  | transversal  (b : Nat) (g : BoolMat)                 -- a local single-qubit transversal gate
  | transversalCNOT (spec : TransversalCNOTSpec)          -- an inter-block incidence-checked logical CNOT
  | transversalCNOTBatch (spec : TransversalCNOTBatchSpec) -- a batched high-rate logical CNOT incidence
  | automorphism (b : Nat) (M : BoolMat)                 -- an arbitrary symplectic logical automorphism
  | switch       (b : Nat) (D : Block) (cert : SwitchCert)      -- a code switch (consumes/transforms b)
  | magic        (ob : MagicObligation)                  -- a deferred, TYPED magic-state obligation (e.g. T)
  | pauli        (q : LQubit) (p : PPM.PLetter)          -- a logical Pauli APPLIED to the carrier (M18: real op, not a frame record)
  deriving Repr

/-- A mixed-IR program. -/
abbrev LogicalExec := List MixedInstr

/-- Is this a (non-executable) magic obligation? -/
def MixedInstr.isMagic : MixedInstr → Bool
  | .magic _ => true
  | _        => false

/-- A program is EXECUTABLE-shaped iff it contains no `.magic` obligation (magic
    type-checks as a deferred obligation but has no `Step` semantics). -/
def progNoMagic (prog : LogicalExec) : Bool := prog.all (fun i => ! i.isMagic)

/-! ## §3. Source gates + cost model + implementation selection. -/

/-- A small source language of logical operations, carrying their operands.

    SYNTAX LEVELS (M13 task 2): a DIRECT transversal is a BLOCK-LEVEL operation —
    `blockTransversal b g` acts on the WHOLE block `b` (every logical qubit of it),
    which is exactly what a physical transversal gate does.  `hGate q`/`sGate q`
    name a single LOGICAL qubit; they are SINGLE-LOGICAL-BLOCK SHORTHAND for the
    direct transversal (honest only when `q`'s block has ONE logical qubit, e.g.
    `tenvQ`) and otherwise lower via the qubit-level PPM teleportation gadget that
    truly acts on `q`.  See the note on `compileOpR`. -/
inductive LogicalOp
  | measure        (r : CVar) (P : MTarget)
  | hGate          (q : LQubit)
  | sGate          (q : LQubit)
  | cnotGate       (control target : LQubit)
  | transversalLogicalCNOT (control target : LQubit) (incidence : BoolMat)
  | transversalLogicalCNOTBatch (controlBlock targetBlock : Nat)
      (incidence logicalIncidence : BoolMat)
  | tGate          (q : LQubit)
  | blockTransversal (b : Nat) (g : BoolMat)   -- a BLOCK-LEVEL direct transversal (acts on all of `b`)
  -- M16 (Pauli / frame level): the bit-/phase-flip Paulis and the controlled-Z.
  -- `xGate`/`zGate` are FRAME operations (lower to a PPM `.frame` update, not a
  -- symplectic basis change); `czGate` is a 2-qubit Clifford (lowers to a gadget).
  | xGate          (q : LQubit)
  | zGate          (q : LQubit)
  | czGate         (control target : LQubit)
  deriving Repr, DecidableEq

/-- Single-qubit symplectic gates (`2×2`, `(x,z)` layout). -/
def hGate2x2 : BoolMat := [[false, true], [true, false]]   -- H : X ↔ Z
def sGate2x2 : BoolMat := [[true, true], [false, true]]     -- S : X ↦ Y, Z ↦ Z

/-! ## §4. Semantics + the direct-fragment correctness theorem.

    For the DIRECT unitary fragment (transversal / automorphism) we give the
    SYMPLECTIC (Heisenberg-picture) semantics: the Clifford map on Pauli vectors.
    A Clifford is determined by this action up to a Pauli/phase, so this is the
    right correctness notion for the symplectic TypeChecker.  Full unitary-with-
    phase equivalence (and a PPM frame-channel semantics) is deferred. -/

/-- The symplectic action of a DIRECT-fragment instruction (`none` for
    PPM/switch/magic, which are not a single pure logical unitary on a block). -/
def MixedInstr.action (Γ : TypedEnv) : MixedInstr → Option BoolMat
  | .transversal b g  => (Γ.block? b).map (fun tb => Internal.transversalMap tb.block.n g)
  | .transversalCNOT spec =>
      match Γ.block? spec.control.blk, Γ.block? spec.target.blk with
      | some cTB, some tTB => some (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
      | _, _ => none
  | .transversalCNOTBatch spec =>
      match Γ.block? spec.controlBlock, Γ.block? spec.targetBlock with
      | some cTB, some tTB => some (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
      | _, _ => none
  | .automorphism _ M => some M
  | _                 => none

/-- Does block `b` have EXACTLY ONE logical qubit (`k = 1`)?  Only then does a
    block-wide transversal coincide with a single-LOGICAL-qubit gate, so only then
    may `hGate`/`sGate` lower directly to a `.transversal` (M14 task 1). -/
def singleLogicalBlock (Γ : TypedEnv) (b : Nat) : Bool :=
  match Γ.block? b with | some tb => tb.block.lx.length == 1 | none => false

end Compiler
