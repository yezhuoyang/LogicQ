/-
  ChainQ.GF2 — GF(2) linear-algebra primitives for the front-end
  type system.  Mathlib-free (pure `Bool`/`List`/`Nat` + `decide`), and
  deliberately name-compatible with `FormalRV.Framework.LDPC`
  (`BoolVec`/`BoolMat`/`dotBit`/`transpose`/`orthogonal`) so the LogicQ
  spec can later be reconciled with the vendored FormalRV `CSSCode` pivot
  without renaming.

  This is the algebra the chain-complex TYPE SYSTEM is built on: the CSS
  commutation condition `H_X · H_Zᵀ = 0` is `orthogonal hx hz`, and the
  chain-complex law `∂₁∘∂₂ = 0` is `isZeroMat (matMul d2 d1)`.
-/

namespace ChainQ.GF2

/-- A GF(2) row vector (`true ↦ 1`, `false ↦ 0`). -/
abbrev BoolVec := List Bool
/-- A GF(2) matrix as a list of equal-length rows. -/
abbrev BoolMat := List BoolVec

/-- GF(2) inner product: `true` iff the number of positions where both are
    `1` is odd (`Σ aᵢ·bᵢ mod 2`).  `dotBit a b = false` ⇔ `a ⟂ b`. -/
def dotBit (a b : BoolVec) : Bool :=
  decide (((a.zip b).countP (fun p => p.1 && p.2)) % 2 = 1)

/-- GF(2) transpose of a matrix with `ncols` columns. -/
def transpose (m : BoolMat) (ncols : Nat) : BoolMat :=
  (List.range ncols).map (fun j => m.map (fun row => row.getD j false))

/-- The GF(2) product `A · Bᵀ`: entry `(i,j)` is `dotBit (row i of a) (row j of b)`. -/
def gemmT (a b : BoolMat) : BoolMat :=
  a.map (fun ra => b.map (fun rb => dotBit ra rb))

/-- The GF(2) product `A · B`, where `bcols` is the column count of `B`
    (`A·B = A · (Bᵀ)ᵀ`). -/
def matMul (a b : BoolMat) (bcols : Nat) : BoolMat :=
  gemmT a (transpose b bcols)

/-- Whether every entry of a matrix is `0`. -/
def isZeroMat (m : BoolMat) : Bool := m.all (fun row => row.all (fun x => ! x))

/-- The CSS commutation / orthogonality test `A · Bᵀ = 0`: every row of `a`
    is GF(2)-orthogonal to every row of `b`. -/
def orthogonal (a b : BoolMat) : Bool :=
  a.all (fun ra => b.all (fun rb => ! dotBit ra rb))

/-- One row of `A·Bᵀ` is all-zero iff that row of `A` is orthogonal to every
    row of `B`. -/
theorem all_not_map_dotBit (ra : BoolVec) (b : BoolMat) :
    (b.map (fun rb => dotBit ra rb)).all (fun x => !x)
      = b.all (fun rb => !dotBit ra rb) := by
  induction b with
  | nil => rfl
  | cons rb tb ih => simp only [List.map_cons, List.all_cons, ih]

/-- **Bridge:** "the GF(2) product `A·Bᵀ` is zero" is exactly the
    orthogonality predicate — the two ways the CSS condition gets written. -/
theorem zero_gemmT_iff_orthogonal (a b : BoolMat) :
    isZeroMat (gemmT a b) = orthogonal a b := by
  unfold isZeroMat gemmT orthogonal
  induction a with
  | nil => rfl
  | cons ra ta ih =>
    simp only [List.map_cons, List.all_cons, all_not_map_dotBit, ih]

/-! ## Smoke checks -/

-- [1,0,1]·[1,1,1] = 1+0+1 = 0 (even overlap → orthogonal).
example : dotBit [true, false, true] [true, true, true] = false := by decide
-- [1,0,0]·[1,1,1] = 1 (odd → non-orthogonal).
example : dotBit [true, false, false] [true, true, true] = true := by decide
example : orthogonal [[true, true, true]] [[true, false, true]] = true := by decide
example : isZeroMat (gemmT [[true, true, true]] [[true, false, true]]) = true := by decide

end ChainQ.GF2
