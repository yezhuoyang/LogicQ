/-
  Compiler.LS.Geometry — patch GEOMETRY metadata for LS / Gidney chunks.

  Preserves the Stim `QUBIT_COORDS(x, y) q` qubit coordinates and the `POLYGON(rgba) q…`
  tile pragmas (e.g. cultivation_stage.py lines 13–28) as METADATA, so the patch
  geometry needed for lattice-surgery-level lowering / visualisation is not lost.

  HONESTY: this is metadata/provenance only.  No geometry SEMANTICS are modelled or
  proven (no adjacency, no planarity, no surgery boundary correctness) — the polygons
  are a DEFERRED visualisation contract.  Mathlib-free.
-/
import Compiler.LS.Syntax

namespace Compiler.LS
open Physical

/-- A physical qubit's spatial coordinate (Stim `QUBIT_COORDS(x, y) q`).  Coordinates
    are `Frac` (rational-capable) so half-integer integration coordinates fit later. -/
structure QubitCoord where
  qubit : PQubit
  x     : Frac
  y     : Frac
  deriving Repr, DecidableEq

/-- A Stim `POLYGON(rgba) q…` pragma: a coloured tile over the listed qubits.  The RGBA
    colour is kept as its raw pragma string — a DEFERRED visualisation contract (no
    rendering / no semantics here). -/
structure Polygon where
  rgba   : String
  qubits : List PQubit
  deriving Repr, DecidableEq

/-- Patch GEOMETRY metadata: qubit coordinates + polygon tiles.  Metadata only. -/
structure Geometry where
  coords   : List QubitCoord := []
  polygons : List Polygon    := []
  deriving Repr, DecidableEq, Inhabited

/-- The `(x, y)` coordinate of a qubit, if recorded. -/
def Geometry.coordOf? (g : Geometry) (q : PQubit) : Option (Frac × Frac) :=
  (g.coords.find? (fun c => c.qubit == q)).map (fun c => (c.x, c.y))

/-- The number of qubits the geometry places. -/
def Geometry.numCoords (g : Geometry) : Nat := g.coords.length

-- a tiny example geometry: qubit 7 sits at (2, 3); an unplaced qubit has no coordinate:
example : Geometry.coordOf? { coords := [⟨0, 0, 0⟩, ⟨7, 2, 3⟩] } 7 = some (2, 3) := by decide
example : Geometry.coordOf? { coords := [⟨0, 0, 0⟩] } 5 = none := by decide

end Compiler.LS
