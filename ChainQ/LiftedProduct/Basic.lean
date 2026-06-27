/-
  ChainQ.LiftedProduct.Basic — the lifted-product raw constructor and its checked
  `?`-variant (Panteleev–Kalachev, arXiv 2012.04068).

  Split out of `ChainQ.Families`; bodies copied verbatim.
-/
import ChainQ.Ring
import ChainQ.Code

namespace ChainQ
open ChainQ.GF2

/-! ## §2. RAW product constructors (⚠ INTERNAL, shape-unchecked). -/
namespace Internal

/-- LP(A, A*) over `F₂[x]/(xˡ−1)` for an `rA×nA` ring matrix `A`:
    `hx = lift[A⊗I | I⊗A*]`, `hz = lift[I⊗A | A*⊗I]`, `n = (rA²+nA²)·ℓ`.
    `hx·hzᵀ = 0` because `transpose (lift A*) = lift A`. -/
def liftedProduct (l : Nat) (A : List (List Circ)) (rA nA : Nat) : CSSCode :=
  let Ad := pDagger l A
  let pHx := pHcat (pKron l A (pIdent nA)) (pKron l (pIdent rA) Ad)
  let pHz := pHcat (pKron l (pIdent nA) A) (pKron l Ad (pIdent rA))
  { n  := (rA * rA + nA * nA) * l,
    hx := liftMat l pHx,
    hz := liftMat l pHz }

end Internal

/-! ## §4. Tests — dimensions, shapes, CSS condition. -/

-- Lifted product tiny: ℓ=3, A = [1, x] (1×2 ring matrix), n = (1+4)·3 = 15.
example : (Internal.liftedProduct 3 [[[0], [1]]] 1 2).n = 15 := by decide
example : (Internal.liftedProduct 3 [[[0], [1]]] 1 2).cssCondition = true := by decide

/-! ## §5. Checked constructors. -/

/-- Checked lifted product: `none` unless `ℓ ≥ 1` and the ring matrix `A` really
    has the declared `rA × nA` shape. -/
def liftedProduct? (l : Nat) (A : List (List Circ)) (rA nA : Nat) : Option CSSCode :=
  if decide (1 ≤ l) && decide (A.length = rA) && A.all (fun row => decide (row.length = nA))
  then some (Internal.liftedProduct l A rA nA) else none

example : (liftedProduct? 3 [[[0], [1]]] 1 2).isSome = true := by decide      -- declared 1×2 = actual
example : (liftedProduct? 3 [[[0], [1]]] 2 2) = none := by decide             -- declared rA=2 ≠ actual 1

end ChainQ
