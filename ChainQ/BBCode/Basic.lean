/-
  ChainQ.BBCode.Basic — the bivariate-bicycle raw constructor and its checked
  `?`-variant.

  GROUNDING NOTE (M22 citation fix): the bivariate-bicycle code family originates
  with Bravyi et al. 2024 (NOT in `Library/`); this `bb` constructor follows the
  BB-style codes AS USED in the universal-adapters paper arXiv 2410.03628 (the
  in-Library source).  Like every family here, the CSS condition is verified
  per-instance by `decide`, not as a ∀-theorem.

  Split out of `ChainQ.Families`; bodies copied verbatim.
-/
import ChainQ.Ring
import ChainQ.Code

namespace ChainQ
open ChainQ.GF2

/-! ## §2. RAW product constructors (⚠ INTERNAL, shape-unchecked). -/
namespace Internal

/-- BB code over `F₂[x,y]/(xˡ−1, yᵐ−1)`: `hx = [A | B]`, `hz = [Bᵀ | Aᵀ]`,
    `n = 2ℓm`.  Since circulants commute, `hx·hzᵀ = A·B + B·A = 0`. -/
def bb (l m : Nat) (a b : List (Nat × Nat)) : CSSCode :=
  let A := biCirculant l m a
  let B := biCirculant l m b
  { n  := 2 * l * m,
    hx := hcat A B,
    hz := hcat (transpose B (l * m)) (transpose A (l * m)) }

end Internal

/-! ## §4. Tests — dimensions, shapes, CSS condition. -/

-- Bivariate bicycle, ℓ=m=3 (n = 18): A = 1 + x + y², B = 1 + x² + y.
example : (Internal.bb 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]).n = 18 := by decide
example : (Internal.bb 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]).cssCondition = true := by decide
example : hasShape (Internal.bb 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]).hx 9 18 = true := by decide

/-! ## §5. Checked constructors. -/

/-- Checked bivariate bicycle: requires `ℓ, m ≥ 1` and nonempty `A`, `B`. -/
def bb? (l m : Nat) (a b : List (Nat × Nat)) : Option CSSCode :=
  if decide (1 ≤ l) && decide (1 ≤ m) && !a.isEmpty && !b.isEmpty
  then some (Internal.bb l m a b) else none

example : (bb? 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]).isSome = true := by decide
example : (bb? 0 3 [(0,0)] [(0,0)]) = none := by decide                       -- ℓ = 0 rejected

end ChainQ
