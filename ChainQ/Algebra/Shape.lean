/-
  ChainQ.Shape — explicit shape predicates and product-construction primitives
  over the GF(2) `BoolVec`/`BoolMat` kernel.

  Motivation (review finding): the kernel's `dotBit`/`transpose`/`matMul` and
  `List.zip`/`getD` silently truncate or pad, so a shape mistake can pass a Bool
  check unnoticed.  This module adds EXPLICIT, checkable shape predicates
  (`matrixWellShaped`, `sameWidth`, `square`, `compatibleMul`, `hasShape`) and
  SAFE accessors (`row?`), plus the algebra needed for parametric code families
  (`identMat`, `zeroMat`, `kron`, block `hcat`/`vcat` with checked variants).
  Lightweight Bool style, Mathlib-free.
-/
import ChainQ.Algebra.GF2

namespace ChainQ.GF2

/-! ## §1. Shapes. -/

/-- Column count = length of the first row (`0` for an empty matrix). -/
def width (m : BoolMat) : Nat := (m.headD []).length
/-- Row count. -/
def height (m : BoolMat) : Nat := m.length

/-- Every row has the same length (`= width m`).  An empty matrix is well-shaped. -/
def matrixWellShaped (m : BoolMat) : Bool := m.all (fun r => decide (r.length = width m))

/-- Explicit shape: `m` has exactly `r` rows, each of length `c`. -/
def hasShape (m : BoolMat) (r c : Nat) : Bool :=
  decide (m.length = r) && m.all (fun row => decide (row.length = c))

/-- `a` and `b` are well-shaped and have the same column count. -/
def sameWidth (a b : BoolMat) : Bool :=
  matrixWellShaped a && matrixWellShaped b && decide (width a = width b)

/-- `m` is a well-shaped `n × n` square matrix. -/
def square (m : BoolMat) (n : Nat) : Bool := hasShape m n n

/-- `a · b` is shape-compatible: `a`'s column count equals `b`'s row count
    (and both are well-shaped). -/
def compatibleMul (a b : BoolMat) : Bool :=
  matrixWellShaped a && matrixWellShaped b && decide (width a = b.length)

/-- SAFE row access — `none` for an out-of-range index (never a silent zero row). -/
def row? (m : BoolMat) (i : Nat) : Option BoolVec := m[i]?

/-! ## §2. Building blocks. -/

/-- The `n × n` identity over GF(2). -/
def identMat (n : Nat) : BoolMat :=
  (List.range n).map (fun i => (List.range n).map (fun j => decide (i = j)))

/-- The `r × c` zero matrix. -/
def zeroMat (r c : Nat) : BoolMat := (List.range r).map (fun _ => List.replicate c false)

/-- Kronecker (tensor) product over GF(2): if `a` is `rₐ×cₐ` and `b` is `r_b×c_b`,
    the result is `(rₐ·r_b) × (cₐ·c_b)`, block `(i,k),(j,l) = a[i][j] ∧ b[k][l]`. -/
def kron (a b : BoolMat) : BoolMat :=
  a.flatMap (fun arow => b.map (fun brow =>
    arow.flatMap (fun x => brow.map (fun y => x && y))))

/-! ## §3. Block concatenation (with checked variants). -/

/-- Horizontal concatenation `[a | b]` (assumes equal row counts — see `hcat?`). -/
def hcat (a b : BoolMat) : BoolMat := (a.zip b).map (fun p => p.1 ++ p.2)

/-- Checked horizontal concatenation: `none` unless `a`, `b` have equal row
    counts (so no row is silently dropped by `zip`). -/
def hcat? (a b : BoolMat) : Option BoolMat :=
  if a.length = b.length then some (hcat a b) else none

/-- Vertical concatenation `[a ; b]` (stacks rows; assumes equal widths). -/
def vcat (a b : BoolMat) : BoolMat := a ++ b

/-- Checked vertical concatenation: `none` unless `a`, `b` are well-shaped with
    equal widths (empty operands are allowed). -/
def vcat? (a b : BoolMat) : Option BoolMat :=
  if matrixWellShaped a && matrixWellShaped b &&
      (a.isEmpty || b.isEmpty || decide (width a = width b)) then some (vcat a b) else none

/-! ## §4. Smoke checks. -/

example : identMat 2 = [[true, false], [false, true]] := by decide
example : kron (identMat 2) (identMat 2) = identMat 4 := by decide
example : kron [[true]] (identMat 3) = identMat 3 := by decide
example : matrixWellShaped [[true, false], [false, true]] = true := by decide
example : matrixWellShaped [[true], [true, false]] = false := by decide        -- ragged → rejected
example : hasShape (zeroMat 2 3) 2 3 = true := by decide
example : hasShape (zeroMat 2 3) 3 2 = false := by decide
example : square (identMat 4) 4 = true := by decide
example : compatibleMul (zeroMat 2 3) (zeroMat 3 4) = true := by decide
example : compatibleMul (zeroMat 2 3) (zeroMat 4 5) = false := by decide       -- 3 ≠ 4 → rejected
example : sameWidth (zeroMat 2 3) (zeroMat 5 3) = true := by decide
example : sameWidth (zeroMat 2 3) (zeroMat 2 4) = false := by decide
example : row? [[true], [false]] 1 = some [false] := by decide
example : row? [[true], [false]] 7 = none := by decide                          -- out of range → none, not 0

end ChainQ.GF2
