/-
  ChainQ.GF2Rank — GF(2) Gaussian elimination: row reduction, rank, and
  row-span membership.  This is the ONE new kernel primitive the type checker
  needs (for stabilizer-preservation / kernel-dimension / injectivity checks).

  Mathlib-free, extends the `ChainQ.GF2` namespace.  Vectors are assumed to
  share a common width (the caller's responsibility, as elsewhere in GF2).
-/
import ChainQ.Algebra.GF2

namespace ChainQ.GF2

/-- Component-wise XOR (GF(2) sum); the longer tail is kept (callers pass
    equal-width vectors). -/
def vecXor : BoolVec → BoolVec → BoolVec
  | [],      v       => v
  | u,       []      => u
  | a :: u,  b :: v  => (xor a b) :: vecXor u v

/-- Index of the first `1` (the pivot column), if any. -/
def firstOne : BoolVec → Option Nat
  | []          => none
  | true  :: _  => some 0
  | false :: t  => (firstOne t).map (· + 1)

/-- Reduce `v` against an RREF `basis` (each row's pivot cleared from the others),
    leaving a residual with `0` at every basis pivot. -/
def reduceInto (basis : List BoolVec) (v : BoolVec) : BoolVec :=
  basis.foldl (fun w b =>
    match firstOne b with
    | some j => if w.getD j false then vecXor w b else w
    | none   => w) v

/-- Insert `v` into an RREF basis: reduce it, and if a fresh pivot remains,
    clear that pivot from existing rows and append the residual. -/
def addToBasis (basis : List BoolVec) (v : BoolVec) : List BoolVec :=
  let w := reduceInto basis v
  match firstOne w with
  | none   => basis
  | some j => (basis.map (fun b => if b.getD j false then vecXor b w else b)) ++ [w]

/-- Row-reduce a matrix to a reduced row-echelon basis of its row span. -/
def rowReduce (m : BoolMat) : BoolMat := m.foldl addToBasis []

/-- GF(2) rank = number of independent rows. -/
def rank (m : BoolMat) : Nat := (rowReduce m).length

/-- Whether a vector is all-zero. -/
def isZeroVec (v : BoolVec) : Bool := v.all (fun b => !b)

/-- Whether `v` lies in the row span of `m` (the central membership test). -/
def inSpan (m : BoolMat) (v : BoolVec) : Bool :=
  isZeroVec (reduceInto (rowReduce m) v)

/-! ## Smoke checks -/

example : rank [[true, false], [false, true]] = 2 := by decide
example : rank [[true, true], [true, true]] = 1 := by decide              -- equal rows
example : inSpan [[true, false], [false, true]] [true, true] = true := by decide
example : inSpan [[true, false]] [false, true] = false := by decide
example : inSpan [[true, true, false], [false, true, true]] [true, false, true] = true := by decide

end ChainQ.GF2
