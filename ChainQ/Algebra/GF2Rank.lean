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

/-- XOR the selected rows, starting from an explicit zero-vector width.  This is
    the executable meaning of a GF(2) coefficient vector. -/
def xorRowsByCoeffWithWidth (w : Nat) (coeffs : BoolVec) (rows : BoolMat) : BoolVec :=
  (coeffs.zip rows).foldl
    (fun acc p => if p.1 then vecXor acc p.2 else acc)
    (List.replicate w false)

/-- XOR selected rows, using the matrix width as the zero-vector width.  For
    empty matrices use `xorRowsByCoeffWithWidth` when the ambient width matters. -/
def xorRowsByCoeff (coeffs : BoolVec) (rows : BoolMat) : BoolVec :=
  xorRowsByCoeffWithWidth (rows.headD []).length coeffs rows

private def unitCoeff (n i : Nat) : BoolVec :=
  (List.range n).map (fun j => decide (j = i))

private def reduceWithWitness
    (basis : List (BoolVec × BoolVec)) (v coeff : BoolVec) : BoolVec × BoolVec :=
  basis.foldl
    (fun acc b =>
      match firstOne b.1 with
      | some j => if acc.1.getD j false then (vecXor acc.1 b.1, vecXor acc.2 b.2) else acc
      | none => acc)
    (v, coeff)

private def addToWitnessBasis
    (basis : List (BoolVec × BoolVec)) (v coeff : BoolVec) : List (BoolVec × BoolVec) :=
  let reduced := reduceWithWitness basis v coeff
  match firstOne reduced.1 with
  | none => basis
  | some j =>
      basis.map
        (fun b =>
          if b.1.getD j false then (vecXor b.1 reduced.1, vecXor b.2 reduced.2) else b) ++
      [reduced]

private def witnessBasisAux (total : Nat) : Nat -> BoolMat -> List (BoolVec × BoolVec) ->
    List (BoolVec × BoolVec)
  | _, [], basis => basis
  | i, row :: rows, basis =>
      witnessBasisAux total (i + 1) rows
        (addToWitnessBasis basis row (unitCoeff total i))

/-- Row-reduced basis carrying coefficient witnesses with respect to the original rows. -/
def rowReduceWithWitness (rows : BoolMat) : List (BoolVec × BoolVec) :=
  witnessBasisAux rows.length 0 rows []

/-- Find GF(2) coefficients whose row combination equals `target`, if one is found
    by Gaussian elimination.  This is row-reduction based, not subset enumeration. -/
def solveInSpan? (rows : BoolMat) (target : BoolVec) : Option BoolVec :=
  let reduced := reduceWithWitness (rowReduceWithWitness rows) target
    (List.replicate rows.length false)
  if isZeroVec reduced.1 then some reduced.2 else none

/-! ## Smoke checks -/

example : rank [[true, false], [false, true]] = 2 := by decide
example : rank [[true, true], [true, true]] = 1 := by decide              -- equal rows
example : inSpan [[true, false], [false, true]] [false, false] = true := by decide
example : inSpan [[true, false], [false, true]] [true, true] = true := by decide
example : inSpan [[true, false]] [true, true] = false := by decide
example : inSpan [[true, true], [true, false]] [false, true] = true := by decide
example : inSpan [[true, false]] [false, true] = false := by decide
example : inSpan [[true, true, false], [false, true, true]] [true, false, true] = true := by decide
example : xorRowsByCoeff [true, true] [[true, false], [false, true]] = [true, true] := by decide
example : solveInSpan? [[true, false], [false, true]] [true, true] = some [true, true] := by decide
example :
    (match solveInSpan? [[true, false], [false, true]] [true, true] with
     | some coeffs =>
         xorRowsByCoeffWithWidth 2 coeffs [[true, false], [false, true]] == [true, true]
     | none => false) = true := by decide
example : solveInSpan? [[true, true], [true, false]] [false, true] = some [true, true] := by decide
example :
    (match solveInSpan? [[true, true], [true, false]] [false, true] with
     | some coeffs =>
         xorRowsByCoeffWithWidth 2 coeffs [[true, true], [true, false]] == [false, true]
     | none => false) = true := by decide
example : solveInSpan? [[true, false]] [true, true] = none := by decide
example : solveInSpan? [] [false, false] = some [] := by decide
example : xorRowsByCoeffWithWidth 2 [] [] = [false, false] := by decide

end ChainQ.GF2
