/-
  Compiler.LS.Chunk — the GENERIC lattice-surgery CHUNK abstraction.

  An `LSChunk` wraps an LS program (which already carries its detector / observable /
  postselection annotations and flow contracts) together with a SOURCE reference, a
  STAGE label, the chunk's patch GEOMETRY, and its deferred obligations.  This is the
  composable unit that surgery lowering assembles — NOT Gidney-specific: it serves any
  QEC code, layout, or magic-state protocol whose surgery is expressed as LS programs.
  (Gidney's cultivation chunks are ONE instance, living in `Compiler/LS/Gidney/*`.)

  HONESTY: a chunk is "real" only insofar as its LS program `check`s and its
  measurements/annotations are faithfully modelled; nothing here claims a chunk is a
  FULL protocol circuit, nor that its flows/detectors are stabilizer-sound (those remain
  deferred obligations).  Mathlib-free.
-/
import Compiler.LS.Check
import Compiler.LS.Geometry
import Compiler.LS.LowerQStab

namespace Compiler.LS
open QStab Physical

/-- A lattice-surgery CHUNK: an LS program plus its provenance, a stage label, the patch
    GEOMETRY, and deferred obligations.  The detector/observable/flow annotations live
    inside `program`.  Generic over the QEC code / layout / protocol. -/
structure LSChunk where
  name        : String                  -- our name for the chunk
  source      : String                  -- the source reference (paper / function + file)
  stage       : String                  -- a stage label (e.g. "cultivation", "injection", "merge")
  program     : Program                 -- the LS program (with its sidecar annotations + flows)
  geometry    : Geometry := {}          -- patch geometry (QUBIT_COORDS / POLYGON metadata)
  obligations : List Obligation := []   -- deferred obligations (extractability, flow soundness, …)
  deriving Repr

/-- Run `LS.check` on the chunk's program. -/
def LSChunk.check (c : LSChunk) : Except LSError Checked := Compiler.LS.check c.program

/-- Does the chunk's LS program check? -/
def LSChunk.checks? (c : LSChunk) : Bool := (LSChunk.check c).toOption.isSome

/-- The chunk's detector annotations. -/
def LSChunk.detectors (c : LSChunk) : List DetectorAnn := c.program.detectors

/-- The chunk's observable annotations. -/
def LSChunk.observables (c : LSChunk) : List (String × List QVar) := c.program.observables

/-- The chunk's flow contracts. -/
def LSChunk.flows (c : LSChunk) : List Flow := c.program.flows

/-- The sparse Pauli measurements the chunk actually performs (its physical `meas`
    operators — proof it is NOT an empty/decorative scaffold). -/
def LSChunk.measurements (c : LSChunk) : List SPauli := c.program.measurements

/-- The number of `TICK` scheduling boundaries preserved in the chunk. -/
def LSChunk.tickCount (c : LSChunk) : Nat := c.program.tickCount

/-! ## Chunk-aware lowering. -/

/-- The result of CHUNK-AWARE lowering: the QStab program, the program-level checked
    `sidecar` (detectors / observables / measurement-kinds / flows / determinism), the
    chunk's patch `geometry`, and the fully-MERGED, deduplicated deferred obligations
    (program obligations ⊕ auto extractability ⊕ chunk-level caveats/contracts). -/
structure LoweredChunk where
  qstab       : QStab.StabilizerProg
  sidecar     : Checked
  geometry    : Geometry
  obligations : List Obligation
  deriving Repr

/-- **Chunk-aware lowering.**  Runs the LS checker, lowers to QStab, AUTOMATICALLY
    attaches the extractability obligations (`lowerCheckedWithExtract`), MERGES the
    chunk-level `obligations` (so a user lowering the chunk cannot skip its caveats /
    contracts), and PRESERVES the geometry + measurement-kind metadata in the sidecar.
    Obligations are deduplicated honestly. -/
def lowerChunkCheckedWithExtract (c : LSChunk) : Except LSError LoweredChunk := do
  let (qstab, sidecar) ← lowerCheckedWithExtract c.program
  let merged := (sidecar.obligations ++ c.obligations).eraseDups
  return { qstab := qstab, sidecar := sidecar, geometry := c.geometry, obligations := merged }

/-- Does the chunk lower (check + extract + merge) successfully? -/
def LSChunk.lowers? (c : LSChunk) : Bool := (lowerChunkCheckedWithExtract c).toOption.isSome

end Compiler.LS
