/-
  ChainQ.Kernel — GF(2) right-kernel basis, quotient bases, and matrix inverse,
  built on the existing `rowReduce`/`rank`/`inSpan` (RREF) machinery.

  These let ChainQ DERIVE logical operators (not just check supplied ones):
  X-logicals live in `ker(Hz) / rowSpan(Hx)`, Z-logicals in `ker(Hx) / rowSpan(Hz)`.
  Mathlib-free; all shape-checked variants reject width mismatches.
-/
import ChainQ.Algebra.GF2Rank
import ChainQ.Algebra.Shape

namespace ChainQ.GF2

/-- A basis of the right kernel `{x ∈ F₂ⁿ : ∀ row r of H, dotBit r x = 0}` — the
    orthogonal complement of the row span of `H`.  Standard RREF
    back-substitution: one basis vector per free column.
    `(kernelBasis H n).length = n − rank H`.  (Caller passes `H` of width `n`.) -/
def kernelBasis (H : BoolMat) (n : Nat) : BoolMat :=
  let R := rowReduce H
  let pivots := R.filterMap firstOne
  let freeCols := (List.range n).filter (fun c => ! pivots.contains c)
  freeCols.map (fun f =>
    (List.range n).map (fun c =>
      if c = f then true
      else match R.find? (fun r => firstOne r == some c) with
           | some r => r.getD f false
           | none   => false))

/-- Shape-checked kernel basis: `none` unless `H` is empty or well-shaped of
    width `n` (so no row is silently truncated/padded). -/
def kernelBasis? (H : BoolMat) (n : Nat) : Option BoolMat :=
  if H.isEmpty || (matrixWellShaped H && decide (width H = n)) then
    some (kernelBasis H n)
  else none

/-! ### ⚠ `Unsafe` — shape-unchecked algebra.

    DO NOT call these from language / type-checker code; use the checked wrappers
    (`quotientBasis?`, `gf2Inv?`) below instead. -/
namespace Unsafe

/-- A maximal subset of `cands` independent modulo the row span of `stab`
    (the logical-operator representatives in `ker H / rowSpan H'`).  Shape-unchecked. -/
def quotientBasis (stab cands : BoolMat) : BoolMat :=
  (cands.foldl (fun (acc : BoolMat × BoolMat) v =>
      if inSpan acc.1 v then acc else (addToBasis acc.1 v, acc.2 ++ [v]))
    (rowReduce stab, [])).2

/-- GF(2) inverse of an `n×n` matrix via augmented (`[M | I]`) row reduction;
    `none` if singular.  Shape-unchecked: assumes `M` is `n×n` and `getD`s its rows. -/
def gf2Inv (M : BoolMat) (n : Nat) : Option BoolMat :=
  let aug := (List.range n).map (fun i => (M.getD i []) ++ (identMat n).getD i [])
  let R := rowReduce aug
  let rows := (List.range n).map (fun i =>
    match R.find? (fun r => firstOne r == some i) with
    | some r => some (r.drop n)
    | none   => none)
  if rows.all Option.isSome then some (rows.filterMap id) else none

end Unsafe

/-! ## Shape-checked wrappers (the SAFE public surface of this module).

    The `Unsafe.*` algebra above is shape-*unchecked* (it `getD`/`zip`s against an
    assumed width).  Prefer these `?`-variants, which reject a malformed shape with
    `none` instead of silently truncating. -/

/-- Checked square inverse: `none` unless `M` is exactly `n×n`. -/
def gf2Inv? (M : BoolMat) (n : Nat) : Option BoolMat :=
  if hasShape M n n then Unsafe.gf2Inv M n else none

/-- Checked quotient basis: `none` unless `stab` and `cands` are well-shaped and
    (when both nonempty) of equal width — so `inSpan`/`vecXor` cannot truncate. -/
def quotientBasis? (stab cands : BoolMat) : Option BoolMat :=
  if (stab.isEmpty || matrixWellShaped stab) && (cands.isEmpty || matrixWellShaped cands) &&
     (stab.isEmpty || cands.isEmpty || decide (width stab = width cands))
  then some (Unsafe.quotientBasis stab cands) else none

/-! ## Smoke checks. -/

-- ker[1,1,0] over F₂³ = span{[1,1,0], [0,0,1]}.
example : kernelBasis [[true, true, false]] 3 = [[true, true, false], [false, false, true]] := by decide
-- ker of the empty matrix = all of F₂ⁿ.
example : kernelBasis [] 2 = identMat 2 := by decide
-- every kernel vector is orthogonal to the rows of H.
example : orthogonal [[true, true, false]] (kernelBasis [[true, true, false]] 3) = true := by decide
-- a self-inverse upper-triangular matrix over F₂.
example : Unsafe.gf2Inv [[true, true], [false, true]] 2 = some [[true, true], [false, true]] := by decide
-- a singular matrix has no inverse.
example : Unsafe.gf2Inv [[true, true], [true, true]] 2 = none := by decide
example : kernelBasis? [[true], [true, false]] 1 = none := by decide   -- ragged H → none

end ChainQ.GF2
