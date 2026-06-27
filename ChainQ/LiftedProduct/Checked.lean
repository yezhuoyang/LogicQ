/-
  ChainQ.LiftedProduct.Checked — the checked lifted-product constructor and its
  executable accept test.

  Split out of `ChainQ.Checked`; bodies copied verbatim.
-/
import ChainQ.Checked.Basic
import ChainQ.LiftedProduct.Basic

namespace ChainQ
open ChainQ.GF2

/-! ## §2. Checked constructors — `Except ChainQError CheckedCSSCode`. -/

/-- Lifted product; rejects `ℓ = 0` and a ring matrix `A` not of the declared
    `rA × nA` shape. -/
def mkLiftedProduct (l : Nat) (A : List (List Circ)) (rA nA : Nat) :
    Except ChainQError CheckedCSSCode :=
  if ! decide (1 ≤ l) then .error (.degenerateParam "lifted product: ℓ must be ≥ 1")
  else if ! (decide (A.length = rA) && A.all (fun row => decide (row.length = nA))) then
    .error (.badDimension "lifted product: A is not the declared rA × nA shape")
  else mkCSS (Internal.liftedProduct l A rA nA)

/-! ## §4. Executable tests (separate from the theorems above). -/

-- accepts:
example : isOk (mkLiftedProduct 3 [[[0], [1]]] 1 2) = true := by decide

end ChainQ
