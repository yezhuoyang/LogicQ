/-
  Compiler.ChainQ2Mixed.Source — the ChainQ-typed source program and its
  elaboration into the existing Mixed-IR compiler input.

  M-A (front-end bridge): a `ChainQProgram` is a list of NAMED ChainQ code-family
  declarations + logical operations that address logical qubits by `(codeName,
  logicalName)`.  `elabProgram?` reuses the existing ChainQ → TypedBlock pipeline
  (`NamedCodeDecl.checkLogicalIndex?` + `checkedIndexToTypedInterface?`) to build a
  `TypedEnv` and resolve every name to an `LQubit`, producing exactly the
  `(TypedEnv × List LogicalOp)` that the existing public compiler `compile?`
  consumes.  No new lowering or proofs — it closes the ChainQ-source gap and proves
  the ChainQ-program → existing-compiler pipe end-to-end.

  The non-deterministic PATH choice (transversal / PPM / code-switch) and the
  SCHEDULE/Layer structure are added in `Path.lean` / `Schedule.lean`; this file is
  the deterministic front-end.
-/
import Compiler.Mixed.Lower.Public
import TypeChecker.Core.Elaborate
import ChainQ.Syntax
import Compiler.CodeSwitch.ProductSurgery

namespace Compiler.ChainQ2Mixed

open Compiler TypeChecker ChainQ Logical Compiler.CodeSwitch

/-- A ChainQ-typed logical operation: it names a code family and (for qubit-level
    ops) a logical qubit within it, exactly as a paper-facing program would.
    These elaborate to the existing `Compiler.LogicalOp`. -/
inductive ChainQOp
  | hGate            (code logical : String)
  | sGate            (code logical : String)
  | xGate            (code logical : String)
  | zGate            (code logical : String)
  | blockTransversalH (code : String)   -- block-wide transversal H (any k)
  | blockTransversalS (code : String)   -- block-wide transversal S (any k)
  deriving Repr

/-- A ChainQ-typed logical program: named code-family declarations (each carrying a
    user logical-qubit indexing) + a straight-line list of logical operations.
    Block ids in the elaborated env are the DECLARATION ORDER positions. -/
structure ChainQProgram where
  decls : List ChainQ.NamedCodeDecl
  ops   : List ChainQOp

/-- Elaborate the declarations (in order) to name-carrying typed interfaces, reusing
    the existing strict ChainQ → TypeChecker bridge. -/
def elabDecls? (decls : List ChainQ.NamedCodeDecl) :
    Except TypeError (List TypedLogicalInterface) :=
  decls.mapM (fun d =>
    match d.checkLogicalIndex? with
    | .error _ =>
        .error (.other s!"ChainQ2Mixed: code '{d.name}' failed to elaborate or index")
    | .ok idx => checkedIndexToTypedInterface? idx)

/-- Resolve a `(codeName, logicalName)` to its `LQubit` `⟨blockIndex, logicalIndex⟩`,
    using declaration order for the block id and the interface's name table for the
    logical index. -/
def resolveLQubit? (decls : List ChainQ.NamedCodeDecl) (ifaces : List TypedLogicalInterface)
    (codeName logicalName : String) : Except TypeError LQubit :=
  match decls.findIdx? (fun d => d.name == codeName) with
  | none => .error (.other s!"ChainQ2Mixed: unknown code '{codeName}'")
  | some blk =>
    match ifaces[blk]? with
    | none => .error (.other s!"ChainQ2Mixed: interface {blk} out of range")
    | some iface =>
      match iface.indexOf? logicalName with
      | none => .error (.other s!"ChainQ2Mixed: unknown logical '{logicalName}' in code '{codeName}'")
      | some idx => .ok ⟨blk, idx⟩

/-- Resolve the block id of a named code (for block-wide operations). -/
def resolveBlock? (decls : List ChainQ.NamedCodeDecl) (codeName : String) : Except TypeError Nat :=
  match decls.findIdx? (fun d => d.name == codeName) with
  | none => .error (.other s!"ChainQ2Mixed: unknown code '{codeName}'")
  | some blk => .ok blk

/-- Resolve one ChainQ op to a `Compiler.LogicalOp`. -/
def resolveOp? (decls : List ChainQ.NamedCodeDecl) (ifaces : List TypedLogicalInterface) :
    ChainQOp → Except TypeError Compiler.LogicalOp
  | .hGate c l => (resolveLQubit? decls ifaces c l).map Compiler.LogicalOp.hGate
  | .sGate c l => (resolveLQubit? decls ifaces c l).map Compiler.LogicalOp.sGate
  | .xGate c l => (resolveLQubit? decls ifaces c l).map Compiler.LogicalOp.xGate
  | .zGate c l => (resolveLQubit? decls ifaces c l).map Compiler.LogicalOp.zGate
  | .blockTransversalH c =>
      (resolveBlock? decls c).map (fun b => Compiler.LogicalOp.blockTransversal b hGate2x2)
  | .blockTransversalS c =>
      (resolveBlock? decls c).map (fun b => Compiler.LogicalOp.blockTransversal b sGate2x2)

/-- **The ChainQ-source front end**: elaborate a ChainQ-typed program into the
    `(TypedEnv × List LogicalOp)` consumed by the existing Mixed-IR compiler. -/
def elabProgram? (prog : ChainQProgram) :
    Except TypeError (TypedEnv × List Compiler.LogicalOp) := do
  let ifaces ← elabDecls? prog.decls
  let Γ : TypedEnv := { blocks := ifaces.map (·.block) }
  let ops ← prog.ops.mapM (resolveOp? prog.decls ifaces)
  return (Γ, ops)

/-- Compile a ChainQ-typed program end-to-end through the existing public compiler.
    The ancilla address seed is placed just past the declared data blocks.

    LEGACY/limited front end (the primary ChainQ→MixIR compiler is
    `Compiler.ChainQ2Mixed.compileChainQToMixIR?`).  WITNESS-GATED for a single public story:
    it takes `List CapabilityWitness` (NOT raw `List Capability`) and converts internally, so a
    raw `.productSurgery` capability can never enter here either. -/
def compileProgram? (mode : Compiler.CompileMode) (ws : List CapabilityWitness) (prog : ChainQProgram) :
    Except TypeError (TypedEnv × List Compiler.LogicalOp) :=
  match elabProgram? prog with
  | .error e => .error e
  | .ok (Γ, ops) =>
    match compile? mode { caps := ws.map CapabilityWitness.toCapability, anc := ⟨prog.decls.length, 0⟩ } Γ ops with
    | .ok _ => .ok (Γ, ops)
    | .error e => .error e

/-! ## §A. End-to-end examples: ChainQ-typed program → existing `compile?`. -/

/-- A bare logical qubit `data`, with a transversal `H; S`. -/
def bareProg : ChainQProgram :=
  { decls := [ChainQ.indexedBareDecl],
    ops   := [.hGate "bare" "data", .sGate "bare" "data"] }

-- elaboration succeeds and the result COMPILES through the existing compiler:
example : ok? (elabProgram? bareProg) = true := by decide
example :
    (match elabProgram? bareProg with
     | .ok (Γ, ops) => sourceCompilable .moduloMagic { caps := [], anc := ⟨1, 0⟩ } Γ ops
     | .error _ => false) = true := by decide
example : ok? (compileProgram? .moduloMagic [] bareProg) = true := by decide

-- a two-logical block `two_logicals` (`left`,`right`): name-resolved logical Paulis.
def twoProg : ChainQProgram :=
  { decls := [ChainQ.indexedTwoLogicalDecl],
    ops   := [.xGate "two_logicals" "left", .zGate "two_logicals" "right"] }

example : ok? (compileProgram? .moduloMagic [] twoProg) = true := by decide

-- name resolution rejects an unknown logical name and an unknown code name.
example : ok? (elabProgram? { decls := [ChainQ.indexedBareDecl], ops := [.hGate "bare" "nope"] }) = false := by decide
example : ok? (elabProgram? { decls := [ChainQ.indexedBareDecl], ops := [.hGate "ghost" "data"] }) = false := by decide

end Compiler.ChainQ2Mixed
