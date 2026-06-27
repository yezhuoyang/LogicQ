/-
  ChainQ.HGPCode.Repetition — classical repetition codes used as input codes for
  the hypergraph-product family.

  Split out of `ChainQ.Families`; bodies copied verbatim.
-/
import ChainQ.GF2

namespace ChainQ
open ChainQ.GF2

/-! ## §1. Classical input codes. -/

/-- Open-boundary distance-`d` repetition code: `(d−1)×d`, row `i` has `1`s at
    columns `i` and `i+1`. -/
def repOpen (d : Nat) : BoolMat :=
  (List.range (d - 1)).map (fun i =>
    (List.range d).map (fun j => decide (j = i) || decide (j = i + 1)))

/-- Cyclic distance-`d` repetition code: `d×d`, row `i` has `1`s at `i`,
    `(i+1) mod d`. -/
def repCyc (d : Nat) : BoolMat :=
  (List.range d).map (fun i =>
    (List.range d).map (fun j => decide (j = i) || decide (j = (i + 1) % d)))

end ChainQ
